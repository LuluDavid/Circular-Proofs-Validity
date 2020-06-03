# CircularProofsValidity
A Formalization attempt of the **Decidability of Circular Proof Validity**

## Which goal ?

The goal is to prove a result from Amina DOUMANE's thesis on infinite proofs, more specifically on
circular proofs, which are *infinite repetitions of the same application of rules* to prove a formula
in µMALL.

To make it short, if you take a sample of linear logic and replace the exponentials (? and !) with
fixed points (greatest fixed point and smallest fixed point), you obtain a logic where you can
allow infinite proofs (and thus circular proofs), but only if you decide of some validity criteria
to **limit the logic's expressivity**. 

Thus, there exists a validity criteria on circular proofs, which is detailed in <a href="http://theses.md.univ-paris-diderot.fr/DOUMANE_Amina_2_va_20170627.pdf">this document</a>
(I might upload a summary later on).

## Inspirations

This implementation is highly inspired from the works of Pierre Letouzey on Natural Deduction
and Olivier Laurent on Linear Logic:

https://gitlab.math.univ-paris-diderot.fr/letouzey/natded

https://github.com/olaure01/yalla/releases/tag/v2.0 (yalla 2.0) 

## Which logical background ?

This implementation of Linear Logic is focused on proving the decidability of the validity
criteria for circular proof, that is why:

1. **FIXED POINTS:** the exponentials ! and ? are here replaced by fixed points 
   (µ/$: least fixed point, v/€ greatest fixed point).
2. **VARS:** we only work with positive second order vars, which means they're invariant by dual.
3. **RENAMING:** for each rule, it is possible to do the same job keeping the current sequent as a 
   further backedgeable sequent once the rule is applied.
4. **BACKEDGING:** the backedge rule is introduced as an axiomatic rule: if the current sequent is 
   s and s's formulas appear striclty in one backedgeable sequents, then the current sequent 
   is proved.
5. **Locally Nameless Encoding:** the vars are seen as bounded debruijn variables or free named 
   variables, thus a variable's "freedom" is deeply encoded here

We will introduce then a second notion of validity, which is the "real" validity criteria,
and once this is done, a side-implementation of omega-automaton will help us demonstrate the 
decidability of the criteria.

## Code structure

About the structure of the code :

* **Defs.v** introduces a few notations for the operators and quantifiers later used.
* **Debruijn.v** introduces the formulas using Debruijn representation for bound variables, 
  also introduces sequents of formulas.
* **Address.v** defines addresses for formulas and a few useful properties for disjointness.
* **Occurrences.v** defines the same notions for occurrences than in Debruijn.v for formulas
* **Derivations.v** delimits in particular the occurrence derivations, and their validity, which
  is a bit more complicated than for simple formulas
* **TreePrelim.v** introduces a tree structure to represent formulas (NOT USED YET)
* **Suboccurrences.v** defines the Suboccurrences of a formula and a few properties on them
* **Subformulas.v** defines the Subformulas of a formula
* **FL-Suboccurrences.v** defines the Fisher-Ladner Suboccurrences of a formula
* **FL-Subformulas.v** defines the Fisher-Ladner Subformulas of a formula
* **Traces.v** introduces the traces directly as streams of consecutive formulas, and contains
  the validity criteria.

Auxiliary Files :
AsciiOrder.v, StringOrder.v, StringUtils.v, Utils.v provide classic useful functions on
Ascii characters, Strings, (lazy) boolean types, etc.
