\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{vivi}[Class for assignments and notes]

%% 选项 Options
% 边数模式 Side mode
\providecommand{\Side}{oneside}% 单边 (不分奇偶数页, 默认) 或双边 (区分奇偶数页) 模式 Oneside (not distinguishing odd or even pages, default) or twoside (distinguishing odd and even pages) mode
\newif\ifTwoSide% [布尔变量] 是否为双边模式 [Bool] Whether twoside mode or not (default)
\DeclareOption{oneside}% 单边模式 Oneside mode
{
    \renewcommand{\Side}{oneside}
    \TwoSidefalse
}
\DeclareOption{twoside}% 双边模式 Twoside mode
{
    \renewcommand{\Side}{twoside}
    \TwoSidetrue
}

% 语言 Language
\newif\ifUsingEnglish% [布尔变量] 是否 (默认) 使用英语 [Bool] Whether using English or not (default)
\DeclareOption{zh}% 使用中文
{
    \UsingEnglishfalse
    \PassOptionsToPackage{scheme=chinese}{ctex}% 用 ctex 宏包汉化文档结构 Chinesize the structure of the file with ctex package
}
\DeclareOption{en}% Using English
{
    \UsingEnglishtrue
    \PassOptionsToPackage{scheme=plain}{ctex}% 阻止 ctex 宏包过度汉化 Suppress excessive chinesization by ctex package
}
\ProcessOptions\relax

% 其余变量传递给 article 类 Other options passed to article class
\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax

%% 加载文档类 Load class
\LoadClass[a4paper, \Side, 12pt]{article}% 加载纸张大小为 A4, \Side 模式, 字号为 12 号的 article 类 Load article class with A4 paper, \Side style and 12pt font

%% 调用宏包 Call packages
\RequirePackage[UTF8]{ctex}% 中文支持 Chinese support
\RequirePackage[vmargin=1in,hmargin=.5in]{geometry}% 页边距 Page margin

% 自定义页眉和页脚 Header and footer customization
\RequirePackage{fancyhdr}% 页眉和页脚 Header & footer
\RequirePackage{xparse}% 多可选参数的自定义命令 Newcommand with multiple optional arguements
\RequirePackage{lastpage}% 返回末页页码 Return page number of the last page
\RequirePackage{calc}% 返回文本宽度 Return width of text
% \RequirePackage[fit]{truncate}% 截断过长文本 Truncate overlong text

% 数学公式 Mathematical equations
\RequirePackage{amsmath, amssymb, amsthm, bm, mathtools}% 基础数学支持, 特殊数学符号, 自定义定理, 公式内加粗 Basic math support, special math symbols, theorem customization, bold in equations
\RequirePackage{mathrsfs}% 公式内花体字母 Non-CM calligraphic letters in equations
\RequirePackage{esint}% 特殊积分号 Special integral signs
\RequirePackage{siunitx}% 格式化物理量 (包括数值和单位) Formatted physical quantities (including values and units)
\RequirePackage[thicklines]{cancel}% 公式内删除线 Cancel lines in equations

% 图片 Figures
\RequirePackage{graphicx}% 插入图片 Insert graphics
\RequirePackage{float}% 强制设定图片位置 Set the positions of figures mandatorily
\RequirePackage{subfigure}% figure环境中子图 Subfigures in the figure environment
\RequirePackage{tikz}% 绘图 Create graphics
% \usetikzlibrary{quantikz}% 绘制量子电路图 (会影响 longtable 环境的正常工作) Plot quantum circuit diagrams (may affect normal performance of longtable environments)

% 表格 Tables
\RequirePackage{multirow}% 表内多行单元格合并 Tables with merged multi-row cells
\RequirePackage{booktabs}% 三线表 Three-line tables
\RequirePackage{longtable}% 表格跨页 Cross-page tables
\RequirePackage{lscape}% 横排表格 Landscape tables
\RequirePackage{diagbox}% 对角线分割单元格 Cells saperated by diagonal lines
\RequirePackage{tabularray}% 表格排版 Table typesetting

% 化学式 Chemstry formulas
\RequirePackage[version=4]{mhchem}% 基础化学式 Basic chemistry equations
\RequirePackage{chemfig}% 化学结构式 Chemistry structural formulas

% 程序代码 Program code
\RequirePackage{listings}
\lstset{
    showstringspaces=false, % 不显示字符串中的空格
	basicstyle=\ttfamily, % 设置字体族
    breaklines=true, % 自动换行
    keywordstyle=\bfseries\color{NavyBlue}, % 设置关键字为粗体，颜色为 NavyBlue
    morekeywords={}, % 设置更多的关键字，用逗号分隔
    emph={self}, % 指定强调词，如果有多个，用逗号隔开
    emphstyle=\bfseries\color{Rhodamine}, % 强调词样式设置
    commentstyle=\itshape\color{black!50!white}, % 设置注释样式，斜体，浅灰色
    stringstyle=\bfseries\color{PineGreen!90!black}, % 设置字符串样式
    columns=flexible,
    numbers=left, % 显示行号在左边
    numbersep=2em, % 设置行号的具体位置
    numberstyle=\footnotesize, % 缩小行号
    frame=single, % 边框
    framesep=1em % 设置代码与边框的距离
}

% 其他 Others
\RequirePackage{ulem}% 各式下划线和删除标记 Various underlines & deletion notes
\normalem% 避免将意大利斜体 (\emph 或 \em) 替换为下划线 Avoide replacing italics (\emph or \em) with underlines
\RequirePackage{color}% 文本颜色 Text color
\RequirePackage{hyperref}% 超链接 Hyperlink% 
\RequirePackage{caption}
\renewcommand{\mathsection}[2]{\section{\texorpdfstring{#1}{#2}}}
\newcommand{\mathsubsection}[2]{\subsection{\texorpdfstring{#1}{#2}}}
\newcommand{\mathsubsubsection}[2]{\subsubsection{\texorpdfstring{#1}{#2}}}
\RequirePackage{framed}% 文本加框 Framed text
\RequirePackage{footmisc}% 脚注引用 Footnote reference
\RequirePackage{enumitem}% 列表 List
\usepackage[dvipsnames]{xcolor} % 颜色 Color

% 首页页眉和页脚 Header & footer
\ifUsingEnglish
    \providecommand{\Name}{Name}% "Name" at the right of the header
    \providecommand{\StudentID}{Student ID}% "Student ID" at the right of the header
    \providecommand{\Grade}{Grade}% "Grade" at the right of the header
\else
    \providecommand{\Name}{姓名}% 页眉右 "姓名"
    \providecommand{\StudentID}{学号}% 页眉右 "学号"
    \providecommand{\Grade}{成绩}% 页眉右 "成绩"
\fi
\pagestyle{fancy}% 全局页眉和页脚风格 Global header and footer style
\fancyhf{}% 清除预设的页眉和页脚 Clear default header and footer
% #1 课程名称 Course name
% #2 课程代码 Course code
% #3 学期 Semeter
% #4 项目标题 Project title
% #5 项目副标题或补充信息 Project subtitle / supplementary information
% #6 姓名 Student name
% #7 姓名上的超链接 Hyperlink on student name
% #8 学号 Student ID
\NewDocumentCommand{\ProjectInfos}{ m m m m m m O{https://github.com/Vivi26499} m }
{
    \fancyhead[C]{#4}% 页眉中 The center of the header
    \ifTwoSide
        \fancyhead[LE]{#1}% 偶数页眉左 The left of even page header
        \fancyhead[RE]{\href{#7}{#6}}% 偶数页眉右 The right of even page header
        \fancyhead[LO]{#8}% 奇数页眉左 The left of odd page header
        \fancyhead[RO]{#2}% 奇数页眉右 The right of odd page header
    \else
        \fancyhead[L]{#1}% 页眉左 The left of the header
        \fancyhead[R]{\href{#7}{#6}}% 页眉右 The right of the header
    \fi
    \setlength{\headheight}{15pt}% 页眉高 Height of the header
    \fancypagestyle{FirstPage}% 首页页眉和页脚风格 First-page header and footer Style
    {
        \fancyhf{}% 清除预设的页眉和页脚 Clear default header and footer
        \setlength{\headheight}{42pt}% 页眉高 Height of the header
        \fancyhead[L]{#1\\
            #2\\
            #3}% 页眉左 The left of the header
        \fancyhead[C]{{\Huge\bfseries#4}\\
            #5}% 页眉中 The center of the header
        \fancyhead[R]{\Name{} : \makebox[\maxof{\widthof{#6}}{\widthof{#8}}][s]{\href{#7}{#6}}\\
            \StudentID{} : \makebox[\maxof{\widthof{#6}}{\widthof{#8}}][s]{#8}\\
            \Grade{} : \underline{\makebox[\maxof{\widthof{#6}}{\widthof{#8}}][s]{}}}% 页眉右 The right of the header
        \fancyfoot[R]{\thepage\ / \getpagerefnumber{LastPage}}% 页脚右: <当前页码> / <总页数> The right of the footer: <current page number> / <total page number>
    }
    \thispagestyle{FirstPage}% 设置首页页眉风格为 FirstPage Set header style of the first page as FirstPage
}
\ifTwoSide
    \fancyfoot[RO]{\thepage\ / \getpagerefnumber{LastPage}}% 奇数页脚右: <当前页码> / <总页数> The right of odd page footer: <current page number> / <total page number>
    \fancyfoot[LE]{\thepage\ / \getpagerefnumber{LastPage}}% 偶数页脚左: <当前页码> / <总页数> The left of even page footer: <current page number> / <total page number>
\else
    \fancyfoot[R]{\thepage\ / \getpagerefnumber{LastPage}}% 页脚右: <当前页码> / <总页数> The right of the footer: <current page number> / <total page number>
\fi

\allowdisplaybreaks[4]% 公式跨页 Cross-page equations
\providecommand{\abs}[1]{\left\lvert#1\right\rvert}% 绝对值 Absolute value
\providecommand{\norm}[1]{\left\lVert#1\right\rVert}% 范数 Norm
\providecommand{\muline}[1]{\text{\uline{$#1$}}}% 公式内下划线 Underlines in equations
\providecommand{\muuline}[1]{\text{\uuline{$#1$}}}% 公式内双下划线 Double underlines in equations
\providecommand{\muwave}[1]{\text{\wave{$#1$}}}% 公式内波浪下划线 Wavy underlines in equations
\providecommand{\msout}[1]{\text{\sout{$#1$}}}% 公式内删除线 Strickout in equations
\providecommand{\mxout}[1]{\text{\xout{$#1$}}}% 公式内删除标记 (多条斜线) Deletion notes (multiple slashes) in equations
\providecommand{\mdashuline}[1]{\text{\dashuline{$#1$}}}% 公式内虚下划线 Dashed underlines in equations
\providecommand{\mdotuline}[1]{\text{\dotuline{$#1$}}}% 公式内点状虚下划线 Dotted underlines in equations
\DeclareMathOperator{\arcsinh}{arcsinh}% 反双曲正弦 Inverse hyperbolic sine
\DeclareMathOperator{\arccosh}{arccosh}% 反双曲余弦 Inverse hyperbolic cosine
\DeclareMathOperator{\arctanh}{arctanh}% 反双曲正切 Inverse hyperbolic tangent
\DeclareMathOperator{\re}{Re}% 复数的实部 Real part of complex number
\DeclareMathOperator{\im}{Im}% 复数的虚部或映射的像 Imaginary part of complex number or image of mapping
\DeclareMathOperator{\sgn}{sgn}% 符号函数 Sign function
\DeclareMathOperator{\sinc}{sinc}% 辛格函数 Sinc function
\DeclareMathOperator{\rect}{rect}% 矩形函数 Rectangular function
\DeclareMathOperator{\tr}{Tr}% 矩阵的迹 Trace of matrix
\DeclareMathOperator{\res}{Res}% 留数 Residue
\DeclareMathOperator{\rank}{rank}% 矩阵的秩 Rank of matrix
\DeclareMathOperator{\grad}{grad}% 梯度 Gradient
\DeclareMathOperator{\Hess}{Hess}% 黑塞矩阵 Hessian matrix
\DeclareMathOperator{\Proj}{Proj}% 投影 Projection
\DeclareMathOperator{\dist}{dist}% 点到集合的距离 Distance from point to set
\DeclareMathOperator{\diag}{diag}% 对角矩阵 Diagonal matrix
\NewDocumentCommand{\dif}{o}{%
  \mathop{}\mathrm{d}\IfValueT{#1}{^{#1}}
}% 微分符号 Differential symbol

% 题目和题解风格 Problem and solution style
\ifUsingEnglish
    \newtheoremstyle{Problem}% Theorem style name
    {}% Space above theorem, being left empty means default
    {}% Space below theorem, being left empty means default
    {}% Theorem body font
    {}% Theorem indent amount
    {\bfseries}% Theorem head font
    {.}% Punctuation after theorem head
    { }% Space after theorem head, whitespace means normal interword space
    {\thmname{#1}\thmnumber{ #2}\thmnote{ (#3)} Score: \underline{\qquad\qquad}}% Theorem head spec, being left empty means default
    \theoremstyle{Problem}% Set theorem style
    \newtheorem{prob}{Problem}[section]% Problem
    \providecommand{\Solution}{Solution}% "Solution" in solution environment (sol)
    \providecommand{\Answer}{Answer}% "Answer" in answer environment (ans)
    \providecommand{\Proof}{Proof}% "Proof" in proof environment (pf)
\else
    \newtheoremstyle{Problem}% 定理风格名称
    {}% 定理上方空间尺寸, 留空为默认
    {}% 定理下方空间尺寸, 留空为默认
    {}% 定理主体字体
    {}% 定理缩进量
    {\bfseries}% 定理开头字体
    {.}% 定理开头后所接标点
    { }% 定理开头后所接空间尺寸, 空格为默认词间距
    {第\thmnumber{#2}\thmname{#1}\thmnote{ (#3)} 得分: \underline{\qquad\qquad}}% 定理开头格式, 留空为默认
    \theoremstyle{Problem}% 设定定理风格
    \newtheorem{prob}{题}% 题目
    \providecommand{\Solution}{解}% 题解环境 (sol) 中的 "解"
    \providecommand{\Answer}{答}% 回答环境 (ans) 中的 "答"
    \providecommand{\Proof}{证}% 证明环境 (pf) 中的 "证"
\fi

\newtheoremstyle{Solution}% 定理风格名称 Theorem style name
{}% 定理上方空间尺寸, 留空为默认 Space above theorem, being left empty means default
{}% 定理下方空间尺寸, 留空为默认 Space below theorem, being left empty means default
{}% 定理主体文本字体 Theorem body font
{}% 定理缩进量 Theorem indent amount
{\bfseries}% 定理开头字体 Theorem head font
{:}% 定理开头后所接标点 Punctuation after theorem head
{ }% 定理开头后所接空间尺寸, 空格为默认词间距 Space after theorem head, whitespace means normal interword space
{\thmname{#1}}% 定理开头格式 Theorem head spec, being left empty means default
\makeatletter
\def\@endtheorem{\qed\endtrivlist\@endpefalse}% 题解末尾添加 QED 符号 (黑色空心小正方形)% Add QED symbols (black hollow small square) to the end of solutions
\makeatother

\theoremstyle{Solution}% 设定定理风格 Set theorem style
\newtheorem*{sol}{\Solution}% 题解 Solution
\newtheorem*{ans}{\Answer}% 回答 Answer
\newtheorem*{pf}{\Proof}% 证明 Proof

\newtheoremstyle{Definition}% 定理风格名称 Theorem style name
{}% 定理上方空间尺寸, 留空为默认 Space above theorem, being left empty means default
{}% 定理下方空间尺寸, 留空为默认 Space below theorem, being left empty means default
{}% 定理主体文本字体 Theorem body font
{}% 定理缩进量 Theorem indent amount
{\color{blue}\bfseries}% 定理开头字体 Theorem head font
{.}% 定理开头后所接标点 Punctuation after theorem head
{ }% 定理开头后所接空间尺寸, 空格为默认词间距 Space after theorem head, whitespace means normal interword space
{\thmname{\color{blue}#1} \thmnumber{\color{blue}#2}}% Theorem head spec, being left empty means default
\makeatletter
\def\@endtheorem{\endtrivlist\@endpefalse}
\makeatother

\theoremstyle{Definition}
\newtheorem{dfn}{Definition}[section]
\newtheorem{thm}[dfn]{Theorem}
\newtheorem{lem}[dfn]{Lemma}

\graphicspath{{Figures/}}% 图片路径 Figure path

% 超链接自动换行 Hyperlink automatic line wrapping
\makeatletter
\def\UrlAlphabet{%
      \do\a\do\b\do\c\do\d\do\e\do\f\do\g\do\h\do\i\do\j%
      \do\k\do\l\do\m\do\n\do\o\do\p\do\q\do\r\do\s\do\t%
      \do\u\do\v\do\w\do\x\do\y\do\z\do\A\do\B\do\C\do\D%
      \do\E\do\F\do\G\do\H\do\I\do\J\do\K\do\L\do\M\do\N%
      \do\O\do\P\do\Q\do\R\do\S\do\T\do\U\do\V\do\W\do\X%
      \do\Y\do\Z}
\def\UrlDigits{\do\1\do\2\do\3\do\4\do\5\do\6\do\7\do\8\do\9\do\0}
\g@addto@macro{\UrlBreaks}{\UrlOrds}
\g@addto@macro{\UrlBreaks}{\UrlAlphabet}
\g@addto@macro{\UrlBreaks}{\UrlDigits}
\makeatother