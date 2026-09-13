# 星形 Kakeya 下界史与迁移材料

先读 [历史梳理全文](KAKEYA_HISTORY.md)，或打开[排版 PDF](https://github.com/subfish-zhou/star-shaped-kakeya-lean/blob/main/history/KAKEYA_HISTORY.pdf)。这份稿件追踪从项目采用的π/98基线到1/10的下界推进：覆盖改进、内外面积相加、径向安排、来源容量、共享终端、合格近端点，以及中间Lean路线与关键修正。

## 阅读入口

- [KAKEYA_HISTORY.md](KAKEYA_HISTORY.md)：本包的中文交付正文，附节点表、Lean入口、证据边界和原件链接。
- [最终正式研究论文](final-public/star-shaped-kakeya-paper.pdf)：已公开的57页研究稿，另含更广的上界研究。
- [最终Lean项目](final-public/README.md)：44模块版本的说明、准备与受控构建入口。
- [历史来源索引](audits/history-source-audit.md)：原路径、阅读行号和当时状态。
- [历史Lean审计](audits/historical-lean-audit.md)：旧端点、import闭包、版本锁和执行证据分级。

## 保存内容

`history/`、`history-sources/`保存选定的普通证明、失败裁决及小型证书；`historical-lean-2026-08-04/`保存冻结历史源码；`snapshot-payload/`保存其他快照的去重载荷；`paper-source/`保存正式论文的可编辑源。以实际文件清单与映射为准。

本包沿用前一版精选材料，并增加完整历史正文、写作修订记录和复述检查。原始几百GB研究树没有被删除或移动。没有搬入`.lake`、对象文件、大数值数据、重复worktree或整个Git数据库。

## 恢复和证据

1. 在新机器解压整个ZIP，保留目录层次，再打开根目录的历史稿；正文的材料链接已逐项检查。
2. `MANIFEST.json`记录本包文件SHA-256和字节数，清单本身不自包含；可用下方命令复核。
3. `SOURCE_MANIFEST.json`记录所选原件身份；`RELOCATION.json`记录原逻辑路径到本包载荷的映射；历史Lean审计JSON中的`restore_map`用于重建不同源码快照。[PORTABLE_RESTORE_MAP.json](PORTABLE_RESTORE_MAP.json)把这193条逻辑记录接到本包实际载荷，逐条核过SHA。不要把同名Lean文件混到同一个快照里，也不要不加选择地照旧绝对路径覆盖文件。
4. 旧原件中的绝对工作树路径和相对链接按原样保留，不等于在新目录可以直接执行。正文的链接指向本包实际文件；恢复旧脚本所需路径时查映射，不恢复整棵旧工作树。
5. 最终项目的`bash prepare.sh`和`python3 build.py`是受控入口。旧工程的聚合Lake命令是历史记录，不作为推荐操作。工具链和上游依赖需按锁在线恢复；本包不是离线工具链镜像。

N32/N64旧端点原始native日志仍有缺口，H历史树缺自身原始manifest；保留了源码及同版本依赖恢复参考。本文没有把旧收据核同写成本次重新运行Lean。

在解压根目录运行：

```sh
python3 -c 'import json,pathlib,hashlib; p=pathlib.Path("."); d=json.loads((p/"MANIFEST.json").read_text(encoding="utf-8")); assert all((p/x["path"]).stat().st_size==x["bytes"] and hashlib.sha256((p/x["path"]).read_bytes()).hexdigest()==x["sha256"] for x in d["files"]); print("PASS",len(d["files"]),"files")'
```

## 写作检查记录

`writing-evidence/`保存英文底本、中文初译、逐轮冻结输入、指定Grok4.6/Gemini3.5Flash的原生回复，以及教师裁决。过程稿、旧BLOCK和模型误读保留历史状态；中文交付稿以根目录`KAKEYA_HISTORY.md`为准。模型复述检查用于找表达与理解问题，不是新的数学证明或人类同行评议。

9月13日本地验收与公开仓库创建是两件有各自证据的事件：早期本地验收文件保留其`public_release=false`，随后公开状态另见`writing-evidence/public-repository-readback.json`。不回写旧记录来制造一条没有转折的历史。

本次公开交付经用户明确授权。旧原件、早期私人迁移说明和当时验收状态按历史版本保留，不能据此误判当前仓库可见性。
