::: {#MathJax_Message style="display: none;"}
:::

::: {.section}
<div>

::: {.block-text block-id="2"}
[**A**]{style="color:rgba(0,0,0,1);"} [**Guarded**]{style="color:rgba(0,0,0,1);"} [**Syntactic**]{style="color:rgba(0,0,0,1);"} [**Model**]{style="color:rgba(0,0,0,1);"} [**of**]{style="color:rgba(0,0,0,1);"} [**Gradual**]{style="color:rgba(0,0,0,1);"} [**Dependent**]{style="color:rgba(0,0,0,1);"} [**Types**]{style="color:rgba(0,0,0,1);"} {#a-guarded-syntactic-model-of-gradual-dependent-types .enlarge}
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
:::

::: {.block-text block-id="3"}
[-we provide a syntactic model of a gradual dependently typed language
in Guarded Cubical Type Theory.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="8"}
[This serves a dual purpose]{style="color:rgba(0,0,0,1);"}

1.  [Implementation]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="9"}
[A syntactic model consists of a semantics-respecting translation from a
gradual language]{style="color:rgba(0,0,0,1);"}
[to]{style="color:rgba(0,0,0,1); background-color:rgba(255,237,38,0.4);"}
[a static dependent language.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="12"}
[This provides a path to implementing a compiler for gradual dependent
types by compiling through a static dependent language\'s existing
compiler.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="14"}
[additionally, it provides a path to fast type-checking, specifically
checking if two types normalize to consistent types. Idris\'s compiler
contains experimental support for evaluating terms at compile-time by
translating them to Chez Scheme, rather than the usual interpreter-style
approach. Translating gradual to static allows such an evaluator to be
used.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="16"}
1.  [Metatheory]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="17"}
[A syntactic model provides a relatively simple way to get a
denotational account of gradual dependent types. It provides a path to
proving the following, which were either difficult or tedious with a
purely operational semantics:]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="18"}
1.  [Proving termination for approximate
    normalization]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="19"}
1.  [Proving the gradual guarantees,]{style="color:rgba(0,0,0,1);"}\
    [and a weak version of New et al\'s]{style="color:rgba(0,0,0,1);"}\
    [groduality. This establishes that
    costs]{style="color:rgba(0,0,0,1);"}\
    [are not \"lossy\" at run-time, and]{style="color:rgba(0,0,0,1);"}\
    [that the guarantees are not satisfied by simply producing? as a
    result for all casts.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="23"}
1.  [Proving fully abstract embedding]{style="color:rgba(0,0,0,1);"}\
    [of the static language. This]{style="color:rgba(0,0,0,1);"}\
    [ensures that reasoning principles]{style="color:rgba(0,0,0,1);"}\
    [that apply in fully static code are]{style="color:rgba(0,0,0,1);"}\
    [not violated when that code is]{style="color:rgba(0,0,0,1);"}\
    [used in gradual contexts]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="26"}
1.  [Proving that the composition operator computes the greatest lower
    bound. This justifies its design, establishing that no precision is
    needlessly lost.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="27"}
[**Extinguishing**]{style="color:rgba(0,0,0,1);"} [**the**]{style="color:rgba(0,0,0,1);"} [**Fire**]{style="color:rgba(0,0,0,1);"} [**Triangle**]{style="color:rgba(0,0,0,1);"}
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
:::

::: {.block-text block-id="32"}
[Lennon-Bertrand et al show no gradual language can
have:]{style="color:rgba(0,0,0,1);"}

1.  [Conservatively extend]{style="color:rgba(0,0,0,1);"}

    [CIC]{style="color:rgba(0,0,0,1);"}

2.  [Strong Normalization]{style="color:rgba(0,0,0,1);"}

3.  [EP Pairs (New et. al.)]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="33"}
1.  [and ③ Are means to an end:]{style="color:rgba(0,0,0,1);"}

[Strong normalization is used to show decidable type-checking, and
EP-Pairs show the gradual guarantees, and that ? is not used as a result
unnecessarily.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="34"}
[Instead, we show ① , along with]{style="color:rgba(0,0,0,1);"}

1.  [Decidable type checking]{style="color:rgba(0,0,0,1);"}
2.  [Costs between precision-related types form a Galois
    Connection]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="35"}
1.  [is achieved with approximate
    normalisation,]{style="color:rgba(0,0,0,1);"}

[so that type-checking computations
terminate.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="38"}
[We use guarded type theory to provide a model of exod run-time
execution while using only terminating computations at the type level.
In the model, terms are represented as pairs of
type:]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-drawing block-id="42"}
:::

::: {.block-text block-id="43"}
[ie. an exact computation under the \"later\" modality of guarded type
theory, paired with a terminating
approximation.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="44"}
1.  [lets us prove the gradual
    guarantees.]{style="color:rgba(0,0,0,1);"}

[We can also show that ? is not produced unnecessarily by showing a
Galois connection for exact execution for a different lattice. For
approx and exact, we have:]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-drawing block-id="46"}
:::

::: {.block-text block-id="47"}
[We \* also \* show the same Galois connection for exact execution, but
for semantic precision defined over the following Boolean
lattice:]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-drawing block-id="48"}
:::

::: {.block-text block-id="49"}
[That is, casting up then down may cause fewer errors, but will never
change the final result. This is a more accurate adaptation of New et
al\'s notion of precision as \"errors less\" to a language with ? as a
term.]{style="color:rgba(0,0,0,1);"}
:::

::: {.block-text block-id="50"}
[**Results**]{style="color:rgba(0,0,0,1);"} [**(**]{style="color:rgba(0,0,0,1);"}[**Hopefully**]{style="color:rgba(0,0,0,1);"}[**)**]{style="color:rgba(0,0,0,1);"}
-------------------------------------------------------------------------------------------------------------------------------------------------------------------
:::

::: {.block-text block-id="51"}
[ ]{.nobr}
:::

::: {.block-drawing block-id="53"}
:::

::: {.block-text block-id="54"}
[Other theorems to prove:]{style="color:rgba(0,0,0,1);"}

-   [Decidable checking]{style="color:rgba(0,0,0,1);"}
-   [Full abstraction]{style="color:rgba(0,0,0,1);"}
-   [Galois connection]{style="color:rgba(0,0,0,1);"}
-   [Weak consistency]{style="color:rgba(0,0,0,1);"}
:::

</div>
:::

<div>

</div>
