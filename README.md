# pyncmc - NCM 音频解码工具

NCM 文件解码为 FLAC/MP3，自动嵌入元数据和封面。

## 特性

- FLAC / MP3 解码，标题、艺人、专辑、歌词与封面自动写入
- 音频起点自适应：NCM 的分隔符存在多种变体，解码前逐种探测并用帧头校验，不依赖固定偏移
- 默认剔除 FLAC 的 `PADDING` 填充块（对齐用的全零块），可用 `--keep-padding` 保留
- 支持单文件、多文件、目录、配置文件四种输入方式，多线程解码

## 安装依赖

```
pip install -r requirements.txt
```

## 用法

### 命令行模式

直接传入文件或目录即可，无需配置文件：

```bash
# 单文件（输出到当前目录）
python pyncmc.py song.ncm

# 单文件 + 输出目录
python pyncmc.py song.ncm ~/Music/

# 多文件
python pyncmc.py a.ncm b.ncm c.ncm

# 多文件 + 输出目录
python pyncmc.py a.ncm b.ncm ~/Music/

# 文件夹（扫描所有支持的音频文件）
python pyncmc.py ./music_folder/

# 文件夹 + 输出目录
python pyncmc.py ./music_folder/ ~/Music/

# 混合：目录 + 文件 + 输出目录
python pyncmc.py "dir1" file.ncm ~/Music/

# 使用 -o 显式指定输出目录
python pyncmc.py song.ncm -o ~/Music/

# 不嵌入元数据（只解码）
python pyncmc.py song.ncm --no-meta

# 保留 FLAC 的 PADDING 填充块（默认剔除）
python pyncmc.py song.ncm --keep-padding

# 自定义线程数
python pyncmc.py song.ncm -t 8 -j 4

# 指定非标准配置文件（CLI 模式也会读取其中的默认值，命令行参数优先）
python pyncmc.py song.ncm -o ~/Music/ -c my_settings.conf
```

### 配置文件模式

不传参数时使用 `music_converter.conf` 批量处理：

```bash
python pyncmc.py
```

配置文件示例：

```ini
[settings]
source_dir = /path/to/source/
target_dir = /path/to/output/
threads = 8
decode_threads = 8
embed_metadata = true
strip_padding = true
log_level = INFO
```

`strip_padding = false` 可保留填充块；命令行下的等价开关是 `--keep-padding`。

### 选项

| 参数 | 说明 |
|------|------|
| `inputs` | 输入文件或目录（留空则配置文件模式） |
| `-o`, `--output` | 输出目录（CLI 模式默认当前目录） |
| `-t`, `--threads` | 单文件解码线程数（默认 4） |
| `-j`, `--jobs` | 文件并行处理数（默认 4） |
| `--no-meta` | 不嵌入元数据 |
| `--keep-padding` | 保留 FLAC 的 `PADDING` 填充块（默认剔除；块体为全零，仅用于对齐文件大小）|
| `-c`, `--config` | 配置文件路径（默认 `music_converter.conf`；CLI 模式也会读它，命令行参数优先）|

---

## analyze_ncm.py - NCM 文件结构分析

```bash
# 单文件
python analyze_ncm.py "KILL SCRIPT - All Night.ncm"

# 文件夹（批量）
python analyze_ncm.py "ncm 所在文件夹"

# 多个指定文件
python analyze_ncm.py "a.ncm" "b.ncm" "c.ncm"

# 指定配置文件（可选）
python analyze_ncm.py "a.ncm" -c my_settings.conf
```

配置文件与 pyncmc 共用同一个 ini，只读取分析相关的键：

```ini
[settings]
# 报告目录；相对路径按脚本所在目录解析
log_dir = logs
# 保留最近多少份报告
log_keep = 20
```

缺省时使用 `logs/` 与 20 份；配置文件不存在时直接回落默认值。
