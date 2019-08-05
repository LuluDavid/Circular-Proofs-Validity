# CircularProofsValidity

This implementation is really close to the works of Pierre Letouzey on Natural Deduction
and Olivier Laurent on Linear Logic:

https://github.com/olaure01/yalla/releases/tag/v2.0 (yalla 2.0) 





This implementation of Linear Logic is focused on proving the decidability of the validity
criteria for circular proofs. That is why : 

1. the exponentials ! and ? are here replaced by fixed points 
   (µ/$: least fixed point, v/€ greatest fixed point).
2. for each rule, there exists an alternative rule doing the same job except it keeps the 
   current sequent as a further backedgeable sequent once the rule is applied.
3. the backedge rule is introduced as an axiomatic rule: if the current sequent is s and
   s appears in the list of backedgeable sequents, then the current sequent is proved.

We will introduce then a second notion of validity, which is the "real" validity criteria,
and once this is done, a side-implementation of omega-automaton will help us demonstrate the 
decidability of the criteria.




About the structure of the code (in the compilation order) :

- AsciiOrder.v, StringOrder.v, StringUtils.v, Utils.v provide classic useful functions on
  Ascii characters, Strings, and (lazy) boolean types.
- Defs.v introduces a few notations for the operators and quantifiers later used.
- Debruijn.v introduces the formulas using Debruijn representation for bound variables, 
  also introduces sequents, rules and derivations of formulas, and their validity.
- Address.v defines addresses for formulas and a few useful properties for disjointness.
- Occurrences.v redefines the same notions for occurrences than in Debruijn.v for formulas
- ODerivations.v delimits in particular the occurrence derivations, and their validity, which
  is a bit more complicated than for formulas
- Suboccurrences.v defines the Suboccurrences of a formula and a few properties on them
- Subformulas.v defines the Subformulas of a formula
- FL-Suboccurrences.v defines the Fisher-Ladner Suboccurrences of a formula
- FL-Subformulas.v defines the Fisher-Ladner Subformulas of a formula

The other files are a few attempts you should not care about.
