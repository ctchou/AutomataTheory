
# AutomataTheory

--------------------------------

This repo contains a Lean4 formalization of automata theory,
where the automata can accept both finite and infinite words.
The theory strives to treat both finite and infinite words in
as uniform a fashion as possible, often using the same automata
construction to prove the same corresponding closure properties
of languages and $\omega$-languages.
Although the ultimate aim is to formalize the theory of finite
automata and the languages and $\omega$-languages they accept,
finiteness assumptions are made only when necessary.

As of 2025-06-09, the following theorems have been proved:

* Regular languages are closed under union, intersection, complementation,
  concatenation, and the Kleene star.

* $\omega$-regular languages are closed under union and intersection.
  Both the concatenation of a regular language followed by an $\omega$-regular
  and the $\omega$-power of a regular language yield an $\omega$-regular language.

The main future goal is to prove that $\omega$-regular languages are closed
under complementation, which is a nontrivial result and will require
significant future work.

--------------------------------

&copy; 2025-present &emsp; Ching-Tsun Chou &emsp; <chingtsun.chou@gmail.com>
