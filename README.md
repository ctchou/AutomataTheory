
# AutomataTheory

--------------------------------

This repo contains a Lean4 formalization of automata theory,
where the automata can "run" on both finite and infinite words.
Our formalization strives to treat both finite and infinite words in
as uniform a fashion as possible, often using the same automata
construction to prove the same or similar closure properties
of languages and $\omega$-languages.
Although our ultimate aim is to formalize the theory of finite
automata and the languages and $\omega$-languages they accept,
finiteness assumptions are made only when necessary.
The main results can be found in `AutomataTheory/Languages/RegLang.lean`,
`AutomataTheory/Languages/OmegaRegLang.lean`, and `AutomataTheory/Languages/DetMullerLang.lean`.

This project was started on 2025-04-03 in a different repo and
migrated to this stand-alone repo on 2025-04-27.

*Update 2025-06-09:* The following results have been proved:

* Regular languages are closed under union, intersection, complementation,
  concatenation, and the Kleene star.

* $\omega$-regular languages are closed under union and intersection.
  Both the concatenation of a regular language followed by an $\omega$-regular language
  and the $\omega$-power of a regular language yield an $\omega$-regular language.

*Update 2025-07-21:* More results have been proved:

* All equivalence classes of a right congruence relation (on finite words)
  of finite index are regular languages.

* A language is $\omega$-regular if and only if it is the union of a finite
  number of languages of the form $U \cdot V^\omega$, where $U$ and $V$ are
  regular languages.

* If a right congruence relation of finite index is "ample" and "saturates"
  an $\omega$-language $L$, then both $L$ and its complement are $\omega$-regular
  (see `AutomataTheory/Congruences/Basic.lean` for the definitions of "ample" and "saturates").

*Update 2025-07-26:* The closure of $\omega$-regular languages under complementation
has been proved, modulo a Ramsey theorem on infinite graphs which is to be proved later.
The proof being formalized is essentially that of Büchi [1] and follows the modern
presentation in the first 2 sections of a survey article by Thomas [3], an outline
of which can also be found in Wikipedia [4].
The crux of the proof uses a congruence relation invented by Büchi
(see `BuchiCongr` defined in `AutomataTheory/Congruences/BuchiCongr.lean`)
that is of finite index and has the ampleness and saturation properties
mentioned above.

*Update 2025-07-30:* The needed Ramsey theorem on infinite graphs has been proved
and there is no `sorry` left.

*Update 2025-08-01:* Significant improvements in notations have been made,
including the more pervasive uses of the dot notation and the introductions of
several infix and postfix operators.

*Update 2025-08-30:* Some results about deterministic automata have been proved:

* A deterministic Büchi automaton accepts precisely the $\omega$-limit of the
  language (on finite words) that it accepts.

* The $\omega$-languages accepted by deterministic Muller automata, referred
  to as deterministic Muller languages, are closed under intersection, union,
  and complementation.

* The $\omega$-limit of a regular language is a deterministic Muller language.

* The concatenation of a regular language and a deterministic Muller language is
  a deterministic Muller language.

The main reference for the above results is a paper by Choueka [2].  In particular,
the last result is proved using Choueka's "flag construction", which is rather subtle.

*Update 2025-09-24:* McNaughton's theorem [5] is proved.  It states that
an $\omega$-language is $\omega$-regular if and only if it is deterministic Muller.
The proof follows Choueka [2] and depends on a key lemma (see `AutomataTheory/Languages/DetMullerLang.lean`)
asserting that for any regular language $V$, there exists another regular language $U$
such that $V^\omega = V^\ast \cdot U\nearrow^\omega$, where $U\nearrow^\omega$ is
the $\omega$-limit of $U$.  As part of this effort, more closure properties of
regular languages are also proved.

[1] Büchi, J.R. (1962). "On a Decision Method in Restricted Second Order Arithmetic".
    The Collected Works of J. Richard Büchi. Stanford: Stanford University Press. pp. 425–435.

[2] Choueka, Yaacov (1974), "Theories of automata on ω-tapes: A simplified approach",
    J. Computer and System Sciences, Vol. 8, pp. 117-141.

[3] Thomas, Wolfgang (1990). "Automata on infinite objects". In Van Leeuwen (ed.).
    Handbook of Theoretical Computer Science. Elsevier. pp. 133–164.

[4] https://en.wikipedia.org/wiki/Büchi_automaton#Complementation

[5] https://en.wikipedia.org/wiki/McNaughton%27s_theorem

--------------------------------

&copy; 2025-present &emsp; Ching-Tsun Chou &emsp; <chingtsun.chou@gmail.com>
