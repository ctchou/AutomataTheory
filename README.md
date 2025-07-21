
# AutomataTheory

--------------------------------

This repo contains a Lean4 formalization of automata theory,
where the automata can "run" both finite and infinite words.
Our formalization strives to treat both finite and infinite words in
as uniform a fashion as possible, often using the same automata
construction to prove the same or similar closure properties
of languages and $\omega$-languages.
Although our ultimate aim is to formalize the theory of finite
automata and the languages and $\omega$-languages they accept,
finiteness assumptions are made only when necessary.

As of 2025-06-09, the following theorems have been proved:

* Regular languages are closed under union, intersection, complementation,
  concatenation, and the Kleene star.

* $\omega$-regular languages are closed under union and intersection.
  Both the concatenation of a regular language followed by an $\omega$-regular
  and the $\omega$-power of a regular language yield an $\omega$-regular language.

As of 2025-07-21, more theorems have been proved:

* All equivalence classes of a (right) congruence relation (on finite words)
  of finite index are regular languages.

* A language is $\omega$-regular if and only if it is the union of a finite
  number of languages of the form $U \cdot V^\omega$, where $U$ and $V$ are
  regular languages.

* If a (right) congruence relation of finite index is "ample" and "saturates"
  an $\omega$-language $L$, then both $L$ and its complement are $\omega$-regular
  (see `AutomataTheory/Congruences/Basic.lean` for the definitions of "ample" and "saturates").

The last result above will allow us to prove that $\omega$-regular languages are closed
under complementation, using a congruence relation invented by J.R. Büchi [1]
(see `Automaton.BuchiCongr` defined in `AutomataTheory/Congruences/BuchiCongr.lean`).
Our formalization follows the first two sections of W. Thomas's survey article [2]
and the Wikipedia article on Büchi automaton [3].

[1] Büchi, J.R. (1962). "On a Decision Method in Restricted Second Order Arithmetic".
    The Collected Works of J. Richard Büchi. Stanford: Stanford University Press. pp. 425–435.

[2] Thomas, Wolfgang (1990). "Automata on infinite objects". In Van Leeuwen (ed.).
    Handbook of Theoretical Computer Science. Elsevier. pp. 133–164.

[3] https://en.wikipedia.org/wiki/Büchi_automaton#Complementation

--------------------------------

&copy; 2025-present &emsp; Ching-Tsun Chou &emsp; <chingtsun.chou@gmail.com>
