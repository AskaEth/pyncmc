#!/usr/bin/env python3
"""
NCM 文件结构分析器 v3
功能：单文件 / 多文件批量分析，终端报告 + 日志存档
用法：python analyze_ncm.py <文件.ncm>           # 单文件
      python analyze_ncm.py <文件夹>             # 多文件
      python analyze_ncm.py <文件1> <文件2> ...  # 多文件
"""

import struct
import sys
import json
import base64
import time
import argparse
import configparser
from pathlib import Path
from typing import Optional, Tuple, List, Dict, Any
from datetime import datetime

try:
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import unpad
    AES_AVAILABLE = True
except ImportError:
    AES_AVAILABLE = False
META_KEY = bytes.fromhex("2331346c6a6b5f215c5d2630553c2728")

JPEG_MAGIC = b'\xff\xd8'
PNG_MAGIC  = b'\x89PNG'
NCM_MAGIC  = b'CTENFDAM'

# ── 终端颜色 ──
class Color:
    RED    = '\033[91m'
    GREEN  = '\033[92m'
    YELLOW = '\033[93m'
    CYAN   = '\033[96m'
    BOLD   = '\033[1m'
    RESET  = '\033[0m'

def c(s, code):
    return f'{code}{s}{Color.RESET}'
    
def strip_ansi(text: str) -> str:
    """移除字符串中的 ANSI 转义序列"""
    import re
    return re.sub(r'\x1b\[[0-9;]*m', '', text)

# ═══════════════════════════════════════════════════════════════
#  工具函数
# ═══════════════════════════════════════════════════════════════

def read_u32(data: bytes, off: int) -> int:
    return struct.unpack('<I', data[off:off + 4])[0]

def find_jpeg(data: bytes, start: int, end: Optional[int] = None) -> int:
    end = end or len(data)
    pos = data.find(JPEG_MAGIC, start, end)
    return pos

def format_size(n: int) -> str:
    if n >= 1024 * 1024:
        return f'{n / 1024 / 1024:.2f} MB'
    elif n >= 1024:
        return f'{n / 1024:.1f} KB'
    return f'{n} B'

def format_duration(ms: int) -> str:
    s = ms // 1000
    m, s = divmod(s, 60)
    return f'{m}:{s:02d}'

def hexdump_line(data: bytes, offset: int = 0) -> str:
    """单行 hexdump，用于报告"""
    hex_part = ' '.join(f'{b:02x}' for b in data[:32])
    ascii_part = ''.join(chr(b) if 32 <= b < 127 else '.' for b in data[:32])
    return f'{offset:08x}  {hex_part:<96s}  |{ascii_part}|'


# ═══════════════════════════════════════════════════════════════
#  元数据解析（与 pyncmc.py 完全一致的 AES 解密版本）
# ═══════════════════════════════════════════════════════════════

def parse_metadata(data: bytes, off: int) -> Tuple[Dict[str, Any], int]:
    """
    解析 NCM 元数据 JSON。
    返回 (metadata_dict, bytes_consumed)。
    """
    if not AES_AVAILABLE:
        # fallback：只尝试裸 base64 -> JSON
        return _parse_metadata_fallback(data, off)

    if off + 4 > len(data):
        return {}, 0

    meta_len = read_u32(data, off)
    offset = off + 4
    consumed = 4

    if meta_len <= 0 or offset + meta_len > len(data):
        return {}, consumed

    encrypted_meta = bytearray(data[offset:offset + meta_len])
    for i in range(len(encrypted_meta)):
        encrypted_meta[i] ^= 0x63

    consumed += meta_len

    # 跳过 22 字节头部
    if len(encrypted_meta) <= 22:
        return {}, consumed

    encrypted_meta = encrypted_meta[22:]

    try:
        b64_str = encrypted_meta.decode('utf-8', errors='ignore')
        b64_str = ''.join(c for c in b64_str if c.isalnum() or c in '+/=')

        if not b64_str:
            return {}, consumed

        padding = 4 - (len(b64_str) % 4)
        if padding != 4:
            b64_str += '=' * padding

        base64_data = base64.b64decode(b64_str)
        cipher = AES.new(META_KEY, AES.MODE_ECB)
        decrypted = cipher.decrypt(base64_data)

        try:
            decrypted = unpad(decrypted, 16)
        except Exception:
            pass

        if len(decrypted) > 6:
            json_str = decrypted[6:].decode('utf-8', errors='ignore')
            start = json_str.find('{')
            end = json_str.rfind('}')
            if start != -1 and end != -1 and end > start:
                json_str = json_str[start:end + 1]
                meta_json = json.loads(json_str)
                return meta_json, consumed

    except Exception:
        pass

    return {}, consumed

def _parse_metadata_fallback(data: bytes, off: int) -> Tuple[Dict[str, Any], int]:
    """无 pycryptodome 时的降级方案（仅适用于部分 NCM 文件）"""
    if off + 4 > len(data):
        return {}, 0

    meta_len = read_u32(data, off)
    offset = off + 4
    consumed = 4

    if meta_len <= 0 or offset + meta_len > len(data):
        return {}, consumed

    encrypted = bytearray(data[offset:offset + meta_len])
    for i in range(len(encrypted)):
        encrypted[i] ^= 0x63

    consumed += meta_len

    if len(encrypted) <= 22:
        return {}, consumed

    encrypted = encrypted[22:]

    try:
        b64_str = encrypted.decode('utf-8', errors='ignore')
        b64_str = ''.join(c for c in b64_str if c.isalnum() or c in '+/=')
        if not b64_str:
            return {}, consumed
        padding = 4 - (len(b64_str) % 4)
        if padding != 4:
            b64_str += '=' * padding
        decoded = base64.b64decode(b64_str)
        meta_json = json.loads(decoded)
        return meta_json, consumed
    except Exception:
        return {}, consumed

def format_artist(artist_val) -> str:
    """将 [[name, id], ...] 格式化为字符串"""
    if isinstance(artist_val, list):
        names = [a[0] if isinstance(a, list) and len(a) > 0 else str(a) for a in artist_val]
        return ' / '.join(names)
    elif isinstance(artist_val, str):
        return artist_val
    return str(artist_val) if artist_val else ''


# ═══════════════════════════════════════════════════════════════
#  封面解析（与 pyncmc.py 完全一致）
# ═══════════════════════════════════════════════════════════════

def parse_cover(data: bytes, off: int) -> Tuple[Optional[bytes], int, str]:
    """
    兼容 NCM 裸格式（B）和盒装格式（A）。
    返回 (cover_data, new_offset, method_description)。
    """
    if off + 4 > len(data):
        return None, off, 'offset 超出文件'

    first = read_u32(data, off)

    # 无封面
    if first <= 0:
        return None, off + 4, f'first_field = {first} → 无封面'

    # ── 格式 B（裸 / 单层） ──
    img_start_b = off + 4
    if first <= 10 * 1024 * 1024 and img_start_b + first <= len(data):
        if data[img_start_b:img_start_b + 2] == JPEG_MAGIC:
            cover = data[img_start_b:img_start_b + first]
            return cover, img_start_b + first, f'格式B（裸） — cover_size = {first:,}'

    # ── 格式 A（盒装 / 双层） ──
    img_start_a = off + 8
    if first >= 8 and off + 4 + first <= len(data):
        inner = read_u32(data, off + 4)
        if 0 < inner <= first - 4:
            if img_start_a + inner <= len(data):
                if data[img_start_a:img_start_a + 2] == JPEG_MAGIC:
                    cover = data[img_start_a:img_start_a + inner]
                    return cover, off + 4 + first, f'格式A（盒装） — box = {first}，cover = {inner:,}'

    # ── 首次 PNG 检查 ──
    if first <= 10 * 1024 * 1024 and img_start_b + first <= len(data):
        if data[img_start_b:img_start_b + 4] == PNG_MAGIC:
            cover = data[img_start_b:img_start_b + first]
            return cover, img_start_b + first, f'格式B（裸/PNG） — cover_size = {first:,}'

    # ── 兜底 ──
    if 0 < first <= 10 * 1024 * 1024:
        return None, off + 4 + first, f'兜底跳过（first_field = {first:,}，非图片）'
    else:
        return None, off + 4, f'first_field = {first} 不合理，仅跳过 4B'


# ═══════════════════════════════════════════════════════════════
#  音频起始偏移多策略探测
# ═══════════════════════════════════════════════════════════════

StrategyResult = Tuple[Optional[bytes], int, str, str]  # (cover, audio_off, cover_method, notes)

def probe_all_strategies(data: bytes, meta_end: int) -> List[Tuple[str, StrategyResult]]:
    """
    尝试多种策略定位封面和音频起点。
    返回 [(策略描述, (cover, audio_offset, cover_method, notes)), ...]
    """
    results = []
    size = len(data)

    # ── 策略 1：CRC32 @ meta_end + 标准分隔符 ──
    sep_std = bytes([0x01, 0x63, 0x05, 0x00, 0x00])
    if meta_end + 9 <= size and data[meta_end + 4:meta_end + 9] == sep_std:
        crc = read_u32(data, meta_end)
        cover_off = meta_end + 9
        cover, new_off, method = parse_cover(data, cover_off)
        results.append((
            'CRC32 + 标准分隔符',
            (cover, new_off, method, f'CRC32 = 0x{crc:08x}')
        ))
    elif meta_end + 5 <= size and data[meta_end:meta_end + 5] == sep_std:
        cover_off = meta_end + 5
        cover, new_off, method = parse_cover(data, cover_off)
        results.append((
            '标准分隔符（无CRC32）',
            (cover, new_off, method, 'CRC32 缺失，分隔符直接位于元数据后')
        ))

    # ── 策略 2：分隔符变体 01 00 00 00 00 ──
    sep_v1 = bytes([0x01, 0x00, 0x00, 0x00, 0x00])
    for label, delta in [('CRC32 + 变体分隔符', 4), ('变体分隔符（无CRC32）', 0)]:
        if meta_end + delta + 5 <= size and data[meta_end + delta:meta_end + delta + 5] == sep_v1:
            crc_info = f'CRC32 = 0x{read_u32(data, meta_end):08x}' if delta == 4 else 'CRC32 缺失'
            cover_off = meta_end + delta + 5
            cover, new_off, method = parse_cover(data, cover_off)
            results.append((
                label,
                (cover, new_off, method, crc_info)
            ))
            break

    # ── 策略 3：盲跳 9 字节（pyncmc.py 当前做法） ──
    for strategy_label, skip in [('盲跳 9B（CRC32 + 分隔符）', 9), ('盲跳 5B（仅分隔符）', 5)]:
        if meta_end + skip <= size:
            sep_bytes = data[meta_end:meta_end + skip]
            cover_off = meta_end + skip
            cover, new_off, method = parse_cover(data, cover_off)
            results.append((
                strategy_label,
                (cover, new_off, method,
                 f'跳过 {skip}B：{sep_bytes.hex()}')
            ))

    # ── 策略 4：JPEG 搜索（终极兜底） ──
    jpeg_pos = find_jpeg(data, meta_end)
    if jpeg_pos != -1 and jpeg_pos < size - 50:
        # 尝试格式 B：前面 4 字节 = cover_size
        if jpeg_pos >= meta_end + 4:
            cs = read_u32(data, jpeg_pos - 4)
            if 0 < cs <= 10 * 1024 * 1024 and jpeg_pos + cs <= size:
                cover = data[jpeg_pos:jpeg_pos + cs]
                results.append((
                    f'JPEG 搜索 → 格式B @ 0x{jpeg_pos:x}',
                    (cover, jpeg_pos + cs, f'JPEG 定位，cover = {cs:,}',
                     f'JPEG @ 0x{jpeg_pos:x}，cover_size @ 0x{jpeg_pos - 4:x}')
                ))
        # 尝试格式 A：前面 8 字节
        if jpeg_pos >= meta_end + 8:
            box = read_u32(data, jpeg_pos - 8)
            inner = read_u32(data, jpeg_pos - 4)
            if 0 < inner <= box - 4 <= 10 * 1024 * 1024:
                cover = data[jpeg_pos:jpeg_pos + inner]
                results.append((
                    f'JPEG 搜索 → 格式A @ 0x{jpeg_pos - 8:x}',
                    (cover, jpeg_pos - 8 + 4 + box, f'JPEG 定位，box = {box}，cover = {inner:,}',
                     f'box @ 0x{jpeg_pos - 8:x}')
                ))

    return results


def pick_best_strategy(results: List[Tuple[str, StrategyResult]]) -> Tuple[Optional[str], Optional[StrategyResult]]:
    """从候选策略中选出最佳结果：优先有封面 + 音频大小合理"""
    best_name, best_result = None, None
    size = 0  # 我们会从外部传入，这里用简单逻辑

    for name, (cover, audio_off, method, notes) in results:
        # 优先：有封面 + 音频起点合理（在文件中间位置）
        if cover is not None:
            if best_result is None or best_result[0] is None:
                best_name, best_result = name, (cover, audio_off, method, notes)
            elif audio_off > (best_result[1] if best_result else 0):
                # 选择封面更大的（更可能是正确的）
                if len(cover) > len(best_result[0] or b''):
                    best_name, best_result = name, (cover, audio_off, method, notes)
        elif best_result is None or best_result[0] is None:
            # 无封面但音频起点合理
            if best_result is None:
                best_name, best_result = name, (cover, audio_off, method, notes)

    return best_name, best_result


# ═══════════════════════════════════════════════════════════════
#  单文件分析
# ═══════════════════════════════════════════════════════════════

FileReport = Dict[str, Any]

def analyze_single(file_path: Path) -> FileReport:
    data = file_path.read_bytes()
    size = len(data)

    report: FileReport = {
        'filename': file_path.name,
        'filepath': str(file_path),
        'file_size': size,
        'valid': False,
        'errors': [],
        'warnings': [],
    }

    # ── 验证魔数 ──
    if size < 8 or data[0:8] != NCM_MAGIC:
        report['errors'].append('非有效的 NCM 文件（魔数不匹配）')
        return report

    report['valid'] = True
    report['gap'] = data[8:10].hex()
    report['key_len'] = read_u32(data, 10)
    off = 14 + report['key_len']

    # ── 元数据 ──
    meta, meta_consumed = parse_metadata(data, off)
    report['meta_offset'] = off
    report['meta_len_raw'] = meta_consumed - 4  # 减去 4 字节长度字段
    report['meta_consumed_total'] = meta_consumed

    if meta:
        report['title'] = meta.get('musicName', meta.get('name', ''))
        report['artist'] = format_artist(meta.get('artist', ''))
        report['album'] = meta.get('album', '')

        # 格式：兼容多种键名
        fmt = (meta.get('format') or
               meta.get('type') or
               meta.get('audioType') or
               meta.get('sfType') or '')
        report['format'] = fmt

        report['bitrate'] = meta.get('bitrate', 0)
        report['duration_ms'] = meta.get('duration', 0)
        
        # 兜底：如果元数据未提供格式，通过比特率推测
        if not report['format']:
            br = report.get('bitrate', 0)
            if br > 320000:
                report['format'] = 'flac'
            elif br > 0:
                report['format'] = 'mp3'
            # 否则保持空字符串
    else:
        report['warnings'].append('元数据解析失败')
        
    off += meta_consumed
    report['meta_end'] = off

    # ── 多策略探测 ──
    results = probe_all_strategies(data, off)
    report['strategies_tried'] = len(results)
    report['all_strategies'] = []

    best_name, best_result = pick_best_strategy(results)

    for name, (cover, audio_off, method, notes) in results:
        is_best = (name == best_name)
        strategy_info = {
            'name': name,
            'cover': cover,
            'audio_offset': audio_off,
            'audio_size': size - audio_off if audio_off < size else 0,
            'cover_method': method,
            'notes': notes,
            'is_best': is_best,
        }
        report['all_strategies'].append(strategy_info)

    if best_result:
        cover, audio_off, method, notes = best_result
        report['best_strategy'] = best_name
        report['audio_offset'] = audio_off
        report['audio_size'] = size - audio_off
        report['cover_data'] = cover
        report['cover_size'] = len(cover) if cover else 0
        report['cover_method'] = method
        report['has_cover'] = cover is not None

        # ── pyncmc 兼容性检查 ──
        # pyncmc 当前从 meta_end 固定跳过 9 字节
        pyncmc_off = off + 9
        pyncmc_cover, pyncmc_new_off, pyncmc_method = parse_cover(data, pyncmc_off)
        report['pyncmc_audio_offset'] = pyncmc_new_off
        report['pyncmc_has_cover'] = pyncmc_cover is not None
        report['pyncmc_cover_size'] = len(pyncmc_cover) if pyncmc_cover else 0
        report['pyncmc_match'] = (
            pyncmc_new_off == audio_off and
            (pyncmc_cover is not None) == (cover is not None)
        )

        if not report['pyncmc_match']:
            report['warnings'].append(
                f'pyncmc.py 兼容性问题：盲跳9B 得到 offset=0x{pyncmc_new_off:x}，'
                f'最优策略 offset=0x{audio_off:x}'
            )
    else:
        report['errors'].append('所有策略均未找到有效的音频起始位置')

    # ── 分隔符信息 ──
    sep_candidates = {}
    for delta in [0, 4]:
        if off + delta + 5 <= size:
            sep = data[off + delta:off + delta + 5]
            if sep[0] == 0x01:
                label = 'CRC32 + 分隔符' if delta == 4 else '仅分隔符'
                sep_candidates[label] = sep.hex()
    report['separators_found'] = sep_candidates

    return report


# ═══════════════════════════════════════════════════════════════
#  报告输出
# ═══════════════════════════════════════════════════════════════

def format_report(reports: List[FileReport], script_dir: Path) -> str:
    """生成完整分析报告文本"""
    lines = []
    W = 70

    now = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    lines.append('╔' + '═' * (W - 2) + '╗')
    lines.append(f'║  NCM 文件结构分析报告{" " * (W - 23)}║')
    lines.append(f'║  生成时间：{now}{" " * (W - 21 - len(now))}║')
    lines.append(f'║  分析文件数：{len(reports)}{" " * (W - 21 - len(str(len(reports))))}║')
    lines.append('╚' + '═' * (W - 2) + '╝')
    lines.append('')

    valid = [r for r in reports if r.get('valid')]
    invalid = [r for r in reports if not r.get('valid')]

    # ── 汇总 ──
    lines.append('─' * W)
    lines.append('  ◆  汇  总')
    lines.append('─' * W)
    lines.append(f'  总文件数：          {len(reports)}')
    lines.append(f'  有效 NCM 文件：     {len(valid)}')
    if invalid:
        lines.append(f'  无效文件：          {len(invalid)}')

    if valid:
        # 分隔符统计
        sep_std = sum(1 for r in valid if r.get('separators_found', {}).get('CRC32 + 分隔符') == '0163050000')
        sep_variant = sum(1 for r in valid if any(
            v == '0100000000' for v in r.get('separators_found', {}).values()
        ))
        lines.append(f'  标准分隔符 (01 63 05 00 00)：{sep_std}')
        if sep_variant:
            lines.append(f'  变体分隔符 (01 00 00 00 00)：{sep_variant}')

        # 封面统计
        with_cover = [r for r in valid if r.get('has_cover')]
        without_cover = [r for r in valid if not r.get('has_cover')]
        lines.append(f'  有封面：            {len(with_cover)} 个')
        lines.append(f'  无封面：            {len(without_cover)} 个')

        if with_cover:
            total_cover_size = sum(r.get('cover_size', 0) for r in with_cover)
            lines.append(f'  封面总大小：        {format_size(total_cover_size)}')

            # 封面格式统计
            format_b = sum(1 for r in with_cover if '格式B' in r.get('cover_method', ''))
            format_a = sum(1 for r in with_cover if '格式A' in r.get('cover_method', ''))
            lines.append(f'  格式B（裸）：       {format_b} 个')
            lines.append(f'  格式A（盒装）：     {format_a} 个')

        # 音频格式统计
        flac_count = sum(1 for r in valid if r.get('format') == 'flac')
        mp3_count = sum(1 for r in valid if r.get('format') == 'mp3')
        if flac_count or mp3_count:
            lines.append(f'  FLAC 音频：         {flac_count} 个')
            lines.append(f'  MP3  音频：         {mp3_count} 个')

        # 兼容性
        compatible = sum(1 for r in valid if r.get('pyncmc_match', False))
        incompatible = sum(1 for r in valid if not r.get('pyncmc_match', True))
        if incompatible:
            lines.append(f'  {c("pyncmc 兼容：", Color.YELLOW)}       {compatible} ✓ / {incompatible} ✗')
        else:
            lines.append(f'  pyncmc 兼容：       {compatible} ✓ / 0 ✗')

    lines.append('')

    # ── 多文件快速一览 ──
    if len(valid) > 1:
        lines.append('─' * W)
        lines.append('  ◆  文件一览')
        lines.append('─' * W)
        # 表头
        header = f'  {"#":<3} {"文件名":<30} {"格式":<5} {"封面":<10} {"大小":<10} {"pyncmc":<8}'
        lines.append(header)
        lines.append('  ' + '─' * (len(header) - 2))
        for i, r in enumerate(valid):
            name = r['filename'][:28] + '..' if len(r['filename']) > 30 else r['filename']
            fmt = r.get('format', '?').upper()
            cover_info = c('✓ ' + format_size(r.get('cover_size', 0)), Color.GREEN) if r.get('has_cover') else c('✗ 无', Color.YELLOW)
            fsize = format_size(r['file_size'])
            compat = c('✓', Color.GREEN) if r.get('pyncmc_match') else c('✗', Color.RED)
            lines.append(f'  {i+1:<3} {name:<30} {fmt:<5} {cover_info:<10} {fsize:<10} {compat:<8}')
        lines.append('')

    # ── 详细分析 ──
    lines.append('─' * W)
    lines.append('  ◆  详细分析')
    lines.append('─' * W)

    for i, r in enumerate(reports):
        lines.append('')
        # 文件标题
        status = c('✓', Color.GREEN) if r.get('valid') else c('✗', Color.RED)
        lines.append(f'  [{i+1}] {status} {r["filename"]}')
        lines.append('  ' + '─' * (W - 4))

        if not r.get('valid'):
            for err in r.get('errors', []):
                lines.append(f'  {c("错误：", Color.RED)}{err}')
            continue

        # 基本信息
        lines.append(f'  文件大小：      {format_size(r["file_size"])}')
        lines.append(f'  密钥长度：      {r["key_len"]} 字节')
        lines.append(f'  元数据长度：    {r.get("meta_len_raw", "?")} 字节')

        # 媒体信息
        if r.get('title'):
            lines.append(f'  标题：          {r["title"]}')
        if r.get('artist'):
            lines.append(f'  艺人：          {r["artist"]}')
        if r.get('album'):
            lines.append(f'  专辑：          {r["album"]}')
        if r.get('format'):
            lines.append(f'  音频格式：      {r["format"].upper()}')
        if r.get('bitrate'):
            lines.append(f'  比特率：        {r["bitrate"] // 1000} kbps')
        if r.get('duration_ms'):
            lines.append(f'  时长：          {format_duration(r["duration_ms"])}')

        # 分隔符
        for label, sep_hex in r.get('separators_found', {}).items():
            is_std = sep_hex == '0163050000'
            indicator = c('标准', Color.GREEN) if is_std else c('变体', Color.YELLOW)
            lines.append(f'  分隔符：        {sep_hex} ({label}，{indicator})')

        # 封面
        if r.get('has_cover'):
            lines.append(f'  {c("封面：", Color.GREEN)}          ✓ {format_size(r["cover_size"])} — {r.get("cover_method", "")}')
        else:
            lines.append(f'  {c("封面：", Color.YELLOW)}          ✗ 无 — {r.get("cover_method", "N/A")}')

        # 音频偏移
        if 'audio_offset' in r:
            lines.append(f'  音频起点：      0x{r["audio_offset"]:08x}')
            lines.append(f'  音频大小：      {format_size(r["audio_size"])}（加密）')

        # 最佳策略
        if r.get('best_strategy'):
            lines.append(f'  最佳策略：      {r["best_strategy"]}')

        # pyncmc 兼容性
        if r.get('pyncmc_match'):
            lines.append(f'  {c("pyncmc 兼容：", Color.GREEN)}  ✓（盲跳9B 可正确处理）')
        else:
            lines.append(f'  {c("pyncmc 兼容：", Color.RED)}  ✗（盲跳9B 与最优策略不一致）')
            lines.append(f'                  最优 offset=0x{r.get("audio_offset", 0):x}，'
                         f'盲跳 offset=0x{r.get("pyncmc_audio_offset", 0):x}')

        # 警告
        for w in r.get('warnings', []):
            lines.append(f'  {c("⚠ " + w, Color.YELLOW)}')

        # 错误
        for e in r.get('errors', []):
            lines.append(f'  {c("✗ " + e, Color.RED)}')

    lines.append('')
    lines.append('─' * W)
    lines.append('  报告结束')
    lines.append('─' * W)

    return '\n'.join(lines)


# ═══════════════════════════════════════════════════════════════
#  主入口
# ═══════════════════════════════════════════════════════════════

def load_analyzer_config(config_path: str) -> Dict[str, Any]:
    """读取 [settings] 里的分析器设置；文件不存在时用默认值。"""
    cfg: Dict[str, Any] = {'log_dir': 'logs', 'log_keep': 20}
    path = Path(config_path)
    if not path.exists():
        return cfg
    try:
        parser = configparser.ConfigParser()
        parser.optionxform = str
        parser.read(path, encoding='utf-8')
        if parser.has_section('settings'):
            section = parser['settings']
            if 'log_dir' in section and section['log_dir'].strip():
                cfg['log_dir'] = section['log_dir'].strip()
            if 'log_keep' in section:
                try:
                    cfg['log_keep'] = max(1, int(section['log_keep']))
                except ValueError:
                    pass
    except Exception as e:
        print(f'⚠ 配置文件读取失败（{e}），使用默认值')
    return cfg


def main():
    ap = argparse.ArgumentParser(
        description='NCM 文件结构分析器',
        epilog='示例：python analyze_ncm.py song.ncm /path/to/ncm_dir -c my.conf')
    ap.add_argument('paths', nargs='*', help='文件或文件夹（可多个）')
    ap.add_argument('-c', '--config', default='music_converter.conf',
                    help='配置文件路径（默认 music_converter.conf）')
    parsed = ap.parse_args()

    if not parsed.paths:
        print('用法：python analyze_ncm.py <文件.ncm 或 文件夹 或 文件1 文件2 ...> [-c 配置文件]')
        sys.exit(1)

    cfg = load_analyzer_config(parsed.config)

    # 收集文件
    ncm_files: List[Path] = []
    args = [Path(a) for a in parsed.paths]

    for arg in args:
        if not arg.exists():
            print(f'⚠ 路径不存在，跳过：{arg}')
            continue
        if arg.is_file() and arg.suffix.lower() == '.ncm':
            ncm_files.append(arg)
        elif arg.is_file():
            print(f'⚠ 非 .ncm 文件，跳过：{arg}')
        elif arg.is_dir():
            found = sorted(arg.glob('*.ncm'))
            ncm_files.extend(found)
            print(f'从文件夹 "{arg}" 找到 {len(found)} 个 NCM 文件')

    if not ncm_files:
        print('未找到任何 .ncm 文件')
        sys.exit(1)

    # 去重
    ncm_files = list(dict.fromkeys(ncm_files))

    print(f'\n正在分析 {len(ncm_files)} 个文件…\n')

    # 逐文件分析
    reports = []
    for f in ncm_files:
        try:
            report = analyze_single(f)
            reports.append(report)
            # 简要进度
            status = c('✓', Color.GREEN) if report.get('valid') else c('✗', Color.RED)
            cover_info = (
                c(f'封面 {format_size(report["cover_size"])}', Color.GREEN)
                if report.get('has_cover') else c('无封面', Color.YELLOW)
            )
            print(f'  {status} {f.name:<45s} {cover_info}')
        except Exception as e:
            reports.append({
                'filename': f.name,
                'filepath': str(f),
                'file_size': f.stat().st_size if f.exists() else 0,
                'valid': False,
                'errors': [f'分析异常：{e}'],
                'warnings': [],
            })
            print(f'  {c("✗", Color.RED)} {f.name:<45s} 分析失败：{e}')

    # ── 生成报告 ──
    script_dir = Path(__file__).resolve().parent
    report_text = format_report(reports, script_dir)

    # 终端输出
    print('\n')
    # 用简单方式输出（避免 Windows 兼容问题）
    for line in report_text.split('\n'):
        print(line)

    # ── 保存日志 ──
    log_dir = Path(cfg['log_dir'])
    if not log_dir.is_absolute():
        log_dir = script_dir / log_dir
    log_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
    log_file = log_dir / f'analysis_{timestamp}.log'
    log_file.write_text(strip_ansi(report_text), encoding='utf-8')
    print(f'\n{c("分析报告已保存到：", Color.CYAN)} {log_file}')

    # 清理旧日志（默认保留最近 20 个，可用 log_keep 调整）
    log_files = sorted(log_dir.glob('analysis_*.log'), key=lambda p: p.stat().st_mtime)
    while len(log_files) > cfg['log_keep']:
        try:
            log_files.pop(0).unlink()
        except Exception:
            pass


if __name__ == '__main__':
    main()
