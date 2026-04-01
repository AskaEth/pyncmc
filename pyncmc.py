#!/usr/bin/env python3
"""
音乐文件转换脚本 - NCM 解码完整版
功能：音频解码 + 元数据嵌入 + 封面嵌入
At: AskaEth
"""

import os
import sys
import shutil
import logging
import configparser
import struct
import hashlib
import time
import json
import base64
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Dict, Set, Tuple, Optional

# 尝试导入加密库
try:
    from Crypto.Cipher import AES
    from Crypto.Util.Padding import unpad
    CRYPTO_AVAILABLE = True
except ImportError as e:
    CRYPTO_AVAILABLE = False
    print(f"警告：pycryptodome 未安装：{e}")
    print("请安装：pip install pycryptodome")

# 尝试导入 mutagen 用于元数据嵌入
MUTAGEN_AVAILABLE = False
MUTAGEN_ERROR = None
try:
    import mutagen
    from mutagen.flac import FLAC, Picture
    from mutagen.mp3 import MP3
    from mutagen.id3 import ID3, TIT2, TPE1, TALB, APIC, USLT, TCON, COMM
    from mutagen.mp4 import MP4
    MUTAGEN_AVAILABLE = True
except ImportError as e:
    MUTAGEN_ERROR = str(e)
    print(f"提示：mutagen 导入失败：{e}")
    print(f"      安装/升级命令：pip install --upgrade mutagen")
except Exception as e:
    MUTAGEN_ERROR = str(e)
    print(f"警告：mutagen 导入失败：{e}")

# 尝试导入 numpy
NUMPY_AVAILABLE = False
try:
    import numpy as np
    NUMPY_AVAILABLE = True
except ImportError:
    pass

# 支持的音频文件扩展名
SUPPORTED_AUDIO_EXT = {'.ncm', '.flac', '.mp3', '.wav', '.m4a', '.aac'}
NCM_OUTPUT_EXT = {'.flac', '.mp3'}

# 分块大小
CHUNK_SIZE = 1024 * 1024  # 1MB

class NCMMetadata:
    """NCM 元数据解析器"""
    
    META_KEY = bytes.fromhex("2331346c6a6b5f215c5d2630553c2728")
    
    def __init__(self):
        self.metadata = {}
        self.cover_data = None
        self.lyrics = None
    
    def parse(self, data: bytes, offset: int) -> int:
        """解析元数据，返回消耗的字节数"""
        if offset + 4 > len(data):
            return 0
        
        meta_len = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        if meta_len <= 0 or offset + meta_len > len(data):
            return 4
        
        encrypted_meta = bytearray(data[offset:offset+meta_len])
        for i in range(len(encrypted_meta)):
            encrypted_meta[i] ^= 0x63
        
        try:
            if len(encrypted_meta) > 22:
                encrypted_meta = encrypted_meta[22:]
                
                try:
                    base64_str = encrypted_meta.decode('utf-8', errors='ignore')
                    base64_str = ''.join(c for c in base64_str if c.isalnum() or c in '+/=')
                    
                    if len(base64_str) > 0:
                        padding = 4 - (len(base64_str) % 4)
                        if padding != 4:
                            base64_str += '=' * padding
                        
                        base64_data = base64.b64decode(base64_str)
                        cipher = AES.new(self.META_KEY, AES.MODE_ECB)
                        decrypted = cipher.decrypt(base64_data)
                        
                        try:
                            decrypted = unpad(decrypted, 16)
                        except:
                            pass
                        
                        if len(decrypted) > 6:
                            json_str = decrypted[6:].decode('utf-8', errors='ignore')
                            start = json_str.find('{')
                            end = json_str.rfind('}')
                            if start != -1 and end != -1 and end > start:
                                json_str = json_str[start:end+1]
                                self.metadata = json.loads(json_str)
                                self._normalize_metadata()
                except Exception as e:
                    logging.debug(f"元数据解析失败：{e}")
        except Exception as e:
            logging.debug(f"元数据处理错误：{e}")
        
        return 4 + meta_len
    
    def _normalize_metadata(self):
        """标准化元数据字段"""
        if 'musicName' in self.metadata:
            self.metadata['title'] = self.metadata['musicName']
        
        if 'artist' in self.metadata:
            if isinstance(self.metadata['artist'], list):
                self.metadata['artists'] = [ar[0] if isinstance(ar, list) else ar 
                                           for ar in self.metadata['artist']]
                self.metadata['artist'] = '/'.join(self.metadata['artists'])
        
        if 'album' in self.metadata:
            self.metadata['album_name'] = self.metadata['album']
        
        if 'albumPic' in self.metadata:
            self.metadata['album_pic_url'] = self.metadata['albumPic']
        
        if 'lyric' in self.metadata:
            self.metadata['lyrics'] = self.metadata['lyric']


class NCMDecoder:
    """NCM 文件解码器 - 完整版"""
    
    CORE_KEY = bytes.fromhex("687a4852416d736f356b496e62617857")
    
    def __init__(self, file_path: Path, decode_threads: int = 4):
        self.file_path = file_path
        self.key_box = bytearray(256)
        self.audio_format = 'mp3'
        self.decode_threads = decode_threads
        self._key_box_array = None
        self.metadata_parser = NCMMetadata()
        self.metadata = {}
        self.cover_data = None
        self.lyrics = None
        
    @staticmethod
    def is_ncm_file(file_path: Path) -> bool:
        try:
            with open(file_path, 'rb') as f:
                header = f.read(8)
                if len(header) < 8:
                    return False
                header1 = struct.unpack('<I', header[0:4])[0]
                header2 = struct.unpack('<I', header[4:8])[0]
                return header1 == 0x4e455443 and header2 == 0x4d414446
        except:
            return False
    
    def _build_key_box(self, key_data: bytes):
        """生成密钥盒"""
        key_len = len(key_data)
        if key_len == 0:
            return
        
        box = bytearray(range(256))
        j = 0
        for i in range(256):
            j = (box[i] + j + key_data[i % key_len]) & 0xff
            box[i], box[j] = box[j], box[i]
        
        for i in range(256):
            i_next = (i + 1) & 0xff
            si = box[i_next]
            sj = box[(i_next + si) & 0xff]
            self.key_box[i] = box[(si + sj) & 0xff]
        
        if NUMPY_AVAILABLE:
            self._key_box_array = np.frombuffer(self.key_box, dtype=np.uint8)
    
    def _xor_decrypt_chunk(self, args: Tuple[bytes, int]) -> Tuple[int, bytes]:
        """XOR 解密单个数据块"""
        data, offset = args
        data_len = len(data)
        
        if NUMPY_AVAILABLE and self._key_box_array is not None:
            data_array = np.frombuffer(data, dtype=np.uint8)
            result = np.empty_like(data_array)
            
            start_pos = offset % 256
            if start_pos == 0 and data_len % 256 == 0:
                key_stream = np.tile(self._key_box_array, data_len // 256)
            else:
                full_repeats = (data_len + start_pos + 255) // 256
                key_stream = np.tile(self._key_box_array, full_repeats)[start_pos:start_pos+data_len]
            
            np.bitwise_xor(data_array, key_stream, out=result)
            return (offset, result.tobytes())
        else:
            result = bytearray(data_len)
            for i in range(data_len):
                result[i] = data[i] ^ self.key_box[(offset + i) & 0xff]
            return (offset, bytes(result))
    
    def _xor_decrypt_multithread(self, data: bytes) -> bytes:
        """多线程 XOR 解密"""
        data_len = len(data)
        
        if data_len < CHUNK_SIZE * 2:
            return self._xor_decrypt_chunk((data, 0))[1]
        
        num_chunks = min(self.decode_threads, (data_len + CHUNK_SIZE - 1) // CHUNK_SIZE)
        chunk_size = (data_len + num_chunks - 1) // num_chunks
        
        tasks = []
        for i in range(num_chunks):
            start = i * chunk_size
            end = min(start + chunk_size, data_len)
            if start >= data_len:
                break
            tasks.append((data[start:end], start))
        
        results = {}
        with ThreadPoolExecutor(max_workers=num_chunks) as executor:
            futures = {executor.submit(self._xor_decrypt_chunk, task): task[1] for task in tasks}
            for future in as_completed(futures):
                offset, decrypted_chunk = future.result()
                results[offset] = decrypted_chunk
        
        decrypted_parts = [results[i * chunk_size] for i in range(num_chunks) if i * chunk_size in results]
        return b''.join(decrypted_parts)
    
    def _parse_cover(self, data: bytes, offset: int) -> Tuple[Optional[bytes], int]:
        """解析封面图片"""
        if offset + 4 > len(data):
            return None, offset
        
        cover_frame_len = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        if cover_frame_len <= 0:
            return None, offset
        
        if offset + 4 > len(data):
            return None, offset
        
        img_len = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        cover_data = None
        if img_len > 0 and offset + img_len <= len(data):
            cover_data = data[offset:offset+img_len]
            offset += img_len
        
        remaining = cover_frame_len - img_len - 4
        if remaining > 0 and offset + remaining <= len(data):
            offset += remaining
        
        return cover_data, offset
    
    def decode(self) -> Tuple[bytes, str, dict]:
        """解码 NCM 文件"""
        if not CRYPTO_AVAILABLE:
            raise ImportError("pycryptodome 未安装")
        
        with open(self.file_path, 'rb') as f:
            data = f.read()
        
        file_size = len(data)
        if file_size < 16:
            raise ValueError("文件太小")
        
        header1 = struct.unpack('<I', data[0:4])[0]
        header2 = struct.unpack('<I', data[4:8])[0]
        
        if header1 != 0x4e455443:
            raise ValueError(f"文件头无效 (NETC): {header1:08x}")
        if header2 != 0x4d414446:
            raise ValueError(f"文件头无效 (MADF): {header2:08x}")
        
        offset = 10
        
        key_len = struct.unpack('<I', data[offset:offset+4])[0]
        offset += 4
        
        if key_len <= 0:
            raise ValueError(f"密钥长度无效：{key_len}")
        
        key_data = bytearray(data[offset:offset+key_len])
        offset += key_len
        
        for i in range(len(key_data)):
            key_data[i] ^= 0x64
        
        cipher = AES.new(self.CORE_KEY, AES.MODE_ECB)
        decrypted = cipher.decrypt(bytes(key_data))
        
        try:
            decrypted = unpad(decrypted, 16)
        except:
            pass
        
        if len(decrypted) < 17:
            raise ValueError("解密后的密钥太短")
        
        self._build_key_box(decrypted[17:])
        
        meta_consumed = self.metadata_parser.parse(data, offset)
        offset += meta_consumed
        self.metadata = self.metadata_parser.metadata
        
        if offset + 5 <= file_size:
            offset += 5
        
        cover_data, offset = self._parse_cover(data, offset)
        if cover_data:
            self.cover_data = cover_data
        
        audio_data = data[offset:]
        
        if len(audio_data) == 0:
            raise ValueError("没有音频数据")
        
        decrypted_audio = self._xor_decrypt_multithread(audio_data)
        
        if decrypted_audio[0:4] == b'fLaC':
            self.audio_format = 'flac'
        else:
            self.audio_format = 'mp3'
        
        info = {
            'metadata': self.metadata,
            'has_cover': self.cover_data is not None,
            'cover_size': len(self.cover_data) if self.cover_data else 0,
            'has_lyrics': 'lyrics' in self.metadata,
        }
        
        return decrypted_audio, self.audio_format, info
    
    def embed_metadata(self, audio_data: bytes, audio_format: str, output_path: Path):
        """将元数据嵌入音频文件"""
        if not MUTAGEN_AVAILABLE:
            with open(output_path, 'wb') as f:
                f.write(audio_data)
            return
        
        try:
            temp_path = output_path.with_suffix(output_path.suffix + '.tmp')
            with open(temp_path, 'wb') as f:
                f.write(audio_data)
            
            if audio_format == 'flac':
                self._embed_flac_metadata(temp_path, output_path)
            elif audio_format == 'mp3':
                self._embed_mp3_metadata(temp_path, output_path)
            elif audio_format in ('m4a', 'aac'):
                self._embed_m4a_metadata(temp_path, output_path)
            else:
                shutil.copy2(temp_path, output_path)
            
            if temp_path.exists():
                temp_path.unlink()
                
        except Exception as e:
            logging.warning(f"嵌入元数据失败：{e}，保存原始文件")
            with open(output_path, 'wb') as f:
                f.write(audio_data)
    
    def _embed_flac_metadata(self, temp_path: Path, output_path: Path):
        """嵌入 FLAC 元数据 (Vorbis Comments)"""
        audio = FLAC(temp_path)
        
        if self.metadata.get('title'):
            audio['title'] = self.metadata['title']
        
        if self.metadata.get('artist'):
            audio['artist'] = self.metadata['artist']
        
        if self.metadata.get('album_name'):
            audio['album'] = self.metadata['album_name']
        
        if self.metadata.get('lyrics'):
            audio['lyrics'] = self.metadata['lyrics']
        
        if self.cover_data:
            pic = Picture()
            pic.type = 3
            pic.mime = 'image/jpeg'
            pic.desc = 'Album Cover'
            pic.data = self.cover_data
            audio.add_picture(pic)
        
        audio.save()
        shutil.copy2(temp_path, output_path)
    
    def _embed_mp3_metadata(self, temp_path: Path, output_path: Path):
        """嵌入 MP3 元数据 (ID3 标签)"""
        try:
            audio = MP3(temp_path, ID3=ID3)
        except:
            audio = MP3(temp_path)
            audio.add_tags()
        
        tags = audio.tags
        
        if self.metadata.get('title'):
            tags['TIT2'] = TIT2(encoding=3, text=self.metadata['title'])
        
        if self.metadata.get('artist'):
            tags['TPE1'] = TPE1(encoding=3, text=self.metadata['artist'])
        
        if self.metadata.get('album_name'):
            tags['TALB'] = TALB(encoding=3, text=self.metadata['album_name'])
        
        if self.metadata.get('lyrics'):
            tags['USLT'] = USLT(encoding=3, lang='chi', desc='Lyrics', text=self.metadata['lyrics'])
        
        if self.cover_data:
            tags['APIC'] = APIC(
                encoding=3,
                mime='image/jpeg',
                type=3,
                desc='Album Cover',
                data=self.cover_data
            )
        
        audio.save()
        shutil.copy2(temp_path, output_path)
    
    def _embed_m4a_metadata(self, temp_path: Path, output_path: Path):
        """嵌入 M4A 元数据 (MP4 原子)"""
        try:
            audio = MP4(temp_path)
        except:
            shutil.copy2(temp_path, output_path)
            return
        
        if self.metadata.get('title'):
            audio['\xa9nam'] = self.metadata['title']
        
        if self.metadata.get('artist'):
            audio['\xa9ART'] = self.metadata['artist']
        
        if self.metadata.get('album_name'):
            audio['\xa9alb'] = self.metadata['album_name']
        
        if self.cover_data:
            audio['covr'] = [self.cover_data]
        
        audio.save()
        shutil.copy2(temp_path, output_path)


def load_config(config_path: str = "music_converter.conf") -> Dict:
    default_config = {
        'source_dir': './folderA',
        'target_dir': './folderB',
        'log_file': 'music_converter.log',
        'log_level': 'INFO',
        'threads': '4',
        'decode_threads': '4',
        'embed_metadata': 'true',
    }
    
    config_path_obj = Path(config_path)
    config = default_config.copy()
    
    if config_path_obj.exists():
        try:
            parser = configparser.ConfigParser()
            parser.optionxform = str
            with open(config_path_obj, 'r', encoding='utf-8') as f:
                parser.read_file(f)
            if parser.has_section('settings'):
                for key in parser.options('settings'):
                    config[key] = parser.get('settings', key)
                print(f"从配置文件读取：{config_path}")
        except Exception as e:
            print(f"警告：配置文件读取失败 ({e})")
    else:
        try:
            parser = configparser.ConfigParser()
            parser['settings'] = default_config
            with open(config_path_obj, 'w', encoding='utf-8') as f:
                parser.write(f)
            print(f"已创建默认配置文件：{config_path}")
        except Exception as e:
            print(f"警告：无法创建配置文件：{e}")
    
    config['source_dir'] = os.path.expanduser(config['source_dir'].strip())
    config['target_dir'] = os.path.expanduser(config['target_dir'].strip())
    
    try:
        config['threads'] = int(config['threads'])
    except ValueError:
        config['threads'] = 4
    
    try:
        config['decode_threads'] = int(config['decode_threads'])
    except ValueError:
        config['decode_threads'] = 4
    
    config['embed_metadata'] = config['embed_metadata'].lower() == 'true'
    
    return config


class FileProcessor:
    def __init__(self, config: Dict):
        self.config = config
        self.source_dir = Path(config['source_dir']).resolve()
        self.target_dir = Path(config['target_dir']).resolve()
        self.logger = self._setup_logging()
        
        self.target_dir.mkdir(parents=True, exist_ok=True)
        self.processed_cache = self._load_processed_cache()
        
        print(f"源目录：{self.source_dir}")
        print(f"目标目录：{self.target_dir}")
        print(f"文件并行线程：{config['threads']}")
        print(f"单文件解码线程：{config['decode_threads']}")
        print(f"嵌入元数据：{config['embed_metadata']}")
        
        if not MUTAGEN_AVAILABLE and config['embed_metadata']:
            print(f"⚠ 警告：embed_metadata=true 但 mutagen 不可用")
            print(f"  错误：{MUTAGEN_ERROR}")
            print(f"  尝试：pip install --upgrade mutagen")
        
        if not self.source_dir.exists():
            print(f"错误：源目录不存在：{self.source_dir}")
    
    def _setup_logging(self) -> logging.Logger:
        logger = logging.getLogger('MusicConverter')
        logger.setLevel(getattr(logging, self.config.get('log_level', 'INFO').upper()))
        logger.handlers = []
        
        file_handler = logging.FileHandler(self.config.get('log_file', 'music_converter.log'), encoding='utf-8')
        file_handler.setFormatter(logging.Formatter('%(asctime)s - %(levelname)s - %(message)s'))
        logger.addHandler(file_handler)
        
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(logging.Formatter('%(levelname)s: %(message)s'))
        logger.addHandler(console_handler)
        
        return logger
    
    def _load_processed_cache(self) -> Set[str]:
        cache_file = self.target_dir / '.processed_cache.json'
        if cache_file.exists():
            try:
                with open(cache_file, 'r', encoding='utf-8') as f:
                    return set(json.load(f))
            except:
                return set()
        return set()
    
    def _save_processed_cache(self):
        cache_file = self.target_dir / '.processed_cache.json'
        try:
            with open(cache_file, 'w', encoding='utf-8') as f:
                json.dump(list(self.processed_cache), f, ensure_ascii=False, indent=2)
        except Exception as e:
            self.logger.warning(f"无法保存缓存：{e}")
    
    def _get_file_signature(self, file_path: Path) -> str:
        try:
            stat = file_path.stat()
            file_info = f"{file_path.name}_{stat.st_size}_{int(stat.st_mtime)}"
            return hashlib.md5(file_info.encode('utf-8')).hexdigest()
        except:
            return ""
    
    def _is_already_processed(self, source_file: Path) -> bool:
        file_sig = self._get_file_signature(source_file)
        if file_sig and file_sig in self.processed_cache:
            return True
        
        base_name = source_file.stem
        if source_file.suffix.lower() == '.ncm':
            for ext in NCM_OUTPUT_EXT:
                target_file = self.target_dir / f"{base_name}{ext}"
                if target_file.exists() and target_file.stat().st_mtime > source_file.stat().st_mtime:
                    return True
        else:
            target_file = self.target_dir / source_file.name
            if target_file.exists() and target_file.stat().st_mtime > source_file.stat().st_mtime:
                return True
        
        return False
    
    def _copy_audio_file(self, source_file: Path) -> bool:
        try:
            target_file = self.target_dir / source_file.name
            if target_file.exists() and target_file.stat().st_mtime > source_file.stat().st_mtime:
                self.logger.info(f"跳过：{source_file.name}")
                return True
            
            shutil.copy2(source_file, target_file)
            self.logger.info(f"已复制：{source_file.name}")
            
            file_sig = self._get_file_signature(source_file)
            if file_sig:
                self.processed_cache.add(file_sig)
            
            return True
        except Exception as e:
            self.logger.error(f"复制失败 {source_file}: {e}")
            return False
    
    def _convert_ncm_file(self, source_file: Path) -> bool:
        try:
            self.logger.info(f"解码：{source_file.name}")
            
            if not NCMDecoder.is_ncm_file(source_file):
                self.logger.error(f"无效的 NCM 文件：{source_file.name}")
                return False
            
            start_time = time.time()
            decoder = NCMDecoder(source_file, self.config.get('decode_threads', 4))
            audio_data, audio_format, info = decoder.decode()
            
            base_name = source_file.stem
            output_file = self.target_dir / f"{base_name}.{audio_format}"
            
            if self.config.get('embed_metadata', False) and MUTAGEN_AVAILABLE:
                decoder.embed_metadata(audio_data, audio_format, output_file)
            else:
                with open(output_file, 'wb') as f:
                    f.write(audio_data)
            
            current_time = time.time()
            os.utime(output_file, (current_time, current_time))
            
            decode_time = time.time() - start_time
            size_mb = len(audio_data) / 1024 / 1024
            speed = size_mb / decode_time if decode_time > 0 else 0
            
            meta_info = []
            if info['metadata'].get('title'):
                meta_info.append(info['metadata']['title'])
            if info['metadata'].get('artist'):
                meta_info.append(info['metadata']['artist'])
            
            log_msg = f"已解码：{source_file.name} -> {base_name}.{audio_format} ({size_mb:.2f}MB, {decode_time:.2f}秒，{speed:.1f}MB/s)"
            if meta_info:
                log_msg += f" [{', '.join(meta_info)}]"
            if info['has_cover']:
                log_msg += f" [封面：{info['cover_size']/1024:.1f}KB]"
            
            self.logger.info(log_msg)
            
            file_sig = self._get_file_signature(source_file)
            if file_sig:
                self.processed_cache.add(file_sig)
            
            return True
            
        except ImportError as e:
            self.logger.error(f"缺少依赖：{e}")
            return False
        except Exception as e:
            self.logger.error(f"解码失败 {source_file}: {e}", exc_info=True)
            return False
    
    def scan_and_process_files(self):
        if not self.source_dir.exists():
            self.logger.error(f"源目录不存在：{self.source_dir}")
            return
        
        audio_files = []
        for ext in SUPPORTED_AUDIO_EXT:
            audio_files.extend(self.source_dir.glob(f"*{ext}"))
            audio_files.extend(self.source_dir.glob(f"*{ext.upper()}"))
        
        audio_files.sort(key=lambda x: x.stat().st_mtime)
        self.logger.info(f"找到 {len(audio_files)} 个文件")
        
        if not audio_files:
            print("没有需要处理的文件")
            return
        
        max_workers = min(self.config.get('threads', 4), len(audio_files), 8)
        success_count = fail_count = skip_count = 0
        
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {}
            
            for file_path in audio_files:
                if self._is_already_processed(file_path):
                    skip_count += 1
                    continue
                
                if file_path.suffix.lower() == '.ncm':
                    future = executor.submit(self._convert_ncm_file, file_path)
                else:
                    future = executor.submit(self._copy_audio_file, file_path)
                
                futures[future] = file_path
            
            for future in as_completed(futures):
                try:
                    if future.result():
                        success_count += 1
                    else:
                        fail_count += 1
                except Exception as e:
                    self.logger.error(f"任务异常：{e}")
                    fail_count += 1
        
        self.logger.info(f"完成：成功 {success_count}, 失败 {fail_count}, 跳过 {skip_count}")
        print(f"完成：成功 {success_count}, 失败 {fail_count}, 跳过 {skip_count}")
        self._save_processed_cache()


def main():
    print("=" * 60)
    print("音乐文件转换工具 - NCM 解码 // By YeiJ")
    print("功能：音频解码 + 元数据嵌入 + 封面嵌入")
    if NUMPY_AVAILABLE:
        print("✓ 使用 numpy 加速")
    if MUTAGEN_AVAILABLE:
        print("✓ 使用 mutagen 嵌入元数据")
    else:
        print(f"⚠ mutagen 不可用：{MUTAGEN_ERROR}")
        print("  安装命令：pip install --upgrade mutagen")
    print("=" * 60)
    
    config = load_config()
    print(f"配置：{config}")
    print("-" * 60)
    
    if not CRYPTO_AVAILABLE:
        print("注意：需要 pycryptodome 库 (pip install pycryptodome)")
    
    try:
        processor = FileProcessor(config)
        processor.scan_and_process_files()
        print("\n完成!")
        return 0
    except KeyboardInterrupt:
        print("\n中断")
        return 130
    except Exception as e:
        print(f"错误：{e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
