# Constructive Foundations and Fixed-Point Compatibility

## Status

This note records a proposed architecture and a conservative logical assessment. It does **not** assert a consistency theorem, verified Agda development, or machine-checked proof.

**Conclusion:** Adding Russian constructivist principles, Bishop-style constructive mathematics, Scott–Ershov domain semantics, and Henkin constructions does not, by itself, establish inconsistency or logical dominance over Scott–Strachey semantics, Lawvere's fixed-point theorem, or the Scott–Kleene fixed-point theorem. Compatibility depends on the exact formal language, axioms, models, and rewrite rules chosen.

## Keep the layers distinct

- **Russian constructivism:** a family of foundations; formal systems may add specific versions of Markov's principle (MP), Church's thesis (CT), or related computability principles. State each principle explicitly.
- **Bishop constructivism:** a constructive mathematical methodology, not one uniquely prescribed axiom list. Formalize the desired constructive content rather than treating the school name as a formula.
- **Scott–Ershov domain theory:** domain-theoretic structures and semantics for partial and recursive computation. Specify the category or order structure, admissible maps, and continuity assumptions.
- **Henkin constructions:** model-construction techniques used in completeness and consistency arguments. A Henkin construction is not, merely by its name, a global rewrite rule or an axiom asserting the truth of every Henkinized formula.
- **Scott–Strachey denotational semantics:** an approach to assigning mathematical meanings to programs, commonly using domains. Distinguish this semantic framework from particular domain-theoretic theorems.
- **Function extensionality:** a principle relating pointwise equality to equality of functions. Its status depends on the underlying type theory; it is compatible with constructive settings, including cubical type theory.
- **Scott–Kleene fixed point:** under suitable hypotheses, a continuous endomap on a pointed omega-CPO has a least fixed point obtained as the supremum of finite iterates from bottom:
  `lfp(f) = sup_n f^n(bottom)`.
  A constructive formalization must provide the chain, its supremum, and the relevant continuity evidence.
- **Lawvere fixed-point theorem:** in a suitable Cartesian closed category, a point-surjective map `e : A -> Y^A` entails that every endomap `u : Y -> Y` has a fixed point. Its point-surjectivity and categorical hypotheses matter; it does not assert that every arbitrary endomap has a fixed point in every category.

## Why inconsistency does not follow

The theorem names above have different logical roles. Some describe methodologies, some describe semantic structures, some are model-construction methods, and some are propositions or theorems with hypotheses. Simply declaring their names as global postulates does not specify a formal theory.

A genuine inconsistency result would require deriving a contradiction from the **explicitly stated** combined assumptions, or exhibiting a known incompatibility between their formalizations. A consistency claim would require an appropriate model or a relative-consistency argument. Neither result follows merely from listing these traditions together.

Likewise, logical dominance needs a precise relation such as entailment, conservative extension, or interpretability. Rewrite-rule dominance needs explicit left- and right-hand sides plus analysis of termination, confluence, and interaction with typing. An axiom is not automatically a computational reduction rule.

## Suggested formalization discipline

1. Choose a base logic or type theory and state its equality rules.
2. Encode each Russian constructivist principle as a separately named, explicitly quantified proposition or axiom.
3. State the Bishop-style constructive definitions and theorems intended; do not encode a school label as an opaque rewrite rule.
4. Define the domain structure (for example, a pointed omega-CPO) and continuity hypotheses explicitly.
5. State Henkinization as a model-construction procedure or formal metatheorem, with its language, consistency assumptions, and witness conditions.
6. Formalize each fixed-point theorem with all hypotheses visible.
7. If adding rewrite rules, define their syntax and orientation, then test termination, confluence, preservation of typing, and interaction with equality.
8. Label the result as a proposal until a proof assistant or metatheoretic argument verifies the claims.

## References

- P. J. Cohen, T. Coquand, S. Huber, and A. Mörtberg, *Cubical Type Theory: A Constructive Interpretation of the Univalence Axiom*, TYPES 2015. https://doi.org/10.4230/LIPIcs.TYPES.2015.5
- Dana S. Scott, work on domains and denotational semantics; use the exact domain category and continuity hypotheses relevant to a formal development.
- F. William Lawvere, *Diagonal arguments and Cartesian closed categories*, in *Category Theory, Homology Theory and their Applications II* (1969), for the categorical fixed-point theorem.
- Bishop-style constructivism and Russian constructivism should be compared through explicit formal systems and principles, not school names alone.

## Review checklist

- [ ] Formal statements replace all school-name placeholders.
- [ ] MP/CT variants are named and their assumptions documented.
- [ ] Henkin construction states its metatheoretic requirements.
- [ ] Domain and fixed-point hypotheses are explicit.
- [ ] Rewrite rules have termination/confluence/type-preservation analysis.
- [ ] No consistency or dominance claim is made without proof.
