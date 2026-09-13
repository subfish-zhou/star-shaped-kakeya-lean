# PDF 排版源

`KAKEYA_HISTORY.tex` 和 `body.tex` 是已实际编译、逐页检查的七页历史 PDF 源。`body.tex` 来自中文定稿的排版版，不是另写的摘要。

在本目录运行 `tectonic -X compile KAKEYA_HISTORY.tex` 可重新生成 PDF。环境需要 Noto Serif/Sans CJK SC、Noto Sans Mono CJK SC、DejaVu Serif/Sans/Sans Mono 系统字体；Tectonic 会按需下载 TeX 宏包。不同字体版本或 PDF 元数据时间可能导致二进制不同。

如需从 Markdown 重建 `body.tex`：去掉历史稿的首行标题（封面单独设置），以 Pandoc 的 `markdown` reader、`latex` writer、`--wrap=none --shift-heading-level-by=-1 --lua-filter=links.lua` 转换。`links.lua` 将本地原件路径变为归档提交永久链接、给长小数提供合法换行点，并保持带空格的命令原样。源码引用标记之间的空格和 `m\*`/`A\*` 转义不可删掉，否则 Markdown 会吞掉引用或把面积记号读成斜体。

主分支 Markdown 使用在线链接；ZIP 内 Markdown 保留本地原件链接。PDF 中95处链接指向同一归档提交的44个原件。新排版未更改数学论断，未重新执行 Lean 或历史数值证书。
