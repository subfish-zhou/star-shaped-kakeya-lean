# 文献地图

检索日期：2026-08-01

## 1. 定义

星形 Kakeya 集 `E ⊂ R²` 满足两条条件：

1. 存在星心 `O ∈ E`，使得对每个 `x ∈ E`，线段 `[O,x]` 全部包含于 `E`。
2. 对每个无向方向 `α mod π`，`E` 包含一条该方向的单位线段。

选定单位线段 `l_α` 后，星形性使三角形 `conv({O} ∪ l_α)` 也包含于 `E`。这把问题转化为控制一族以共同顶点 `O` 为顶点的单位底边三角形之并。

它与普通 Besicovitch/Kakeya 集不同。普通平面 Kakeya 集可以有任意小面积。星形约束强迫所有方向通过同一星心建立径向联系，已知下界因此为正。

Li 2026 对不可测集合使用二维 Lebesgue 外测度 `L²*`，对圆截面使用一维 Hausdorff 外测度。当前研究也应保持这一口径，不能悄悄加入可测性假设。

## 2. 已发表主线

### Cunningham 与 Schoenberg 1965

F. Cunningham Jr. and I. J. Schoenberg, "On The Kakeya Constant", Canadian Journal of Mathematics 17 (1965), 946-956.

- DOI: https://doi.org/10.4153/CJM-1965-090-x
- 论文研究可连续转动单位针的单连通区域，并给出极限构造
  `(5 - 2√2)π/24 = (0.09048...)π`。
- 构造由奇数个旋转单元组成。其区域是星形的，因此也给星形问题提供上界。
- 作者当时猜测该常数可能最优，但没有证明正下界。

### Cunningham 1971

F. Cunningham Jr., "The Kakeya Problem for Simply Connected and for Star-Shaped Sets", The American Mathematical Monthly 78(2) (1971), 114-129.

- DOI: https://doi.org/10.1080/00029890.1971.11992708
- 已知结论：星形 Kakeya 集满足面积下界 `π/108`。
- 原文当前无法从出版社页面匿名下载，但题录由 Crossref 和 OpenAlex 核验，Li 2026 明确引用并复述该定理。

### Li 2026

Shaoqi Li, "An improved lower bound for star-shaped Kakeya sets", Annales Fennici Mathematici 51 (2026), 377-392.

- DOI: https://doi.org/10.54330/afm.185132
- arXiv: https://arxiv.org/abs/2509.05711v2
- 定理：每个星形 Kakeya 集满足 `L²*(E) ≥ π/98`。
- 证明先推广 Cunningham 的截断圆估计，再用圆截面、方向集外测度和内外区域二分改进常数。
- 论文第 4 节给出进一步优化、迭代和双积分方向，但这些 remarks 不是更强的已证明主定理。

arXiv 元数据核验：v1 发布于 2025-09-06，v2 更新于 2026-05-29。Crossref 登记的期刊发表日期是 2026-05-29。

## 3. 截至检索日的文献状态

Crossref 对精确主题的结果主要返回 Cunningham-Schoenberg 1965、Cunningham 1971 和 Li 2026。OpenAlex 记录 Li 论文的引用数为 0，Crossref 的 `is-referenced-by-count` 也是 0。Semantic Scholar API 本次请求遇到 429，未作为否定证据。

这只能支持一个带日期的表述：本轮检索没有发现 2026-08-01 以前已发表的更强星形 Kakeya 上下界。它不能证明不存在未索引预印本，也不能建立归档结果的历史优先权。

## 4. 归档提出的新主张

归档的下界主张是：

```text
L²*(E) > 100π/5599 > π/56
```

它比 Li 的 `π/98` 强，但目前是项目内 paper draft，不是外部文献结论。

归档的最好有限上界是 `E_51`：

```text
area(E_51)/π < 0.09047481313467504
area(E_51) < (904748131346751 / 10^16)π < 19π/210
```

它严格改进 Cunningham-Schoenberg 常数，但目前没有 fresh independent audit，也没有完整 Lean internalization。

## 5. 一手来源

- Li 2026 arXiv v2 PDF：`sources/li-2026-arxiv-2509.05711v2.pdf`
- Cunningham-Schoenberg 1965 PDF：`sources/cunningham-schoenberg-1965.pdf`
- Besicovitch 1928 DOI：https://doi.org/10.1007/BF01171101
- Cunningham 1971 DOI：https://doi.org/10.1080/00029890.1971.11992708
- Cunningham-Schoenberg 1965 DOI：https://doi.org/10.4153/CJM-1965-090-x
- Li 2026 DOI：https://doi.org/10.54330/afm.185132
