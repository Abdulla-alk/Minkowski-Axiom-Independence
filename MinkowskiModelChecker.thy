theory MinkowskiModelChecker
  imports MinkowskiTheoremProving "HOL.Complex_Main"
begin

(*─────────────────────────────────────────────────────────────────────────*)
section ‹Finite slices of Minkowski space›

type_synonym point = "real × real"

text ‹The future order: “go north‑east”.›
definition Rel :: "point ⇒ point ⇒ bool"  (infix "≼" 50) where
  "p ≼ q ⟷ (fst p < fst q ∧ snd p < snd q)"


locale Finite_Minkowski =
  fixes W   :: "point set"                     ― ‹worlds (finite)›
    and Val :: "'p ⇒ point ⇒ bool"             ― ‹valuation›
  assumes finite_W: "finite W"
      and  closed: "⟦ p ≼ q;  p ∈ W ⟧ ⟹ q ∈ W"
begin

lemma trans:  "p ≼ q ⟹ q ≼ r ⟹ p ≼ r"
  by (auto simp: Rel_def)

lemma irrefl: "¬(p ≼ p)"
  by (simp add: Rel_def)

lemma dense:
  assumes "p ≼ r" and "p ≠ r"
  shows   "∃q∈W. p ≼ q ∧ q ≼ r ∧ q ≠ p ∧ q ≠ r"
proof -
  obtain x1 y1 x2 y2 where p: "p=(x1,y1)" and r: "r=(x2,y2)" by (cases p, cases r)
  with assms have "x1 ≤ x2 ∧ y1 ≤ y2 ∧ (x1<x2 ∨ y1<y2)" by (auto simp: Rel_def)
  then consider "x1 < x2" | "y1 < y2" by linarith
  thus ?thesis
  proof cases
    case 1
    let ?q = "((x1+x2)/2, y1)"
    have "?q ∈ W" using closed[of p ?q] assms p r 1
      by (auto simp: Rel_def)
    moreover have "p ≼ ?q ∧ ?q ≼ r ∧ ?q ≠ p ∧ ?q ≠ r"
      using 1 assms p r by (auto simp: Rel_def)
    ultimately show ?thesis by blast
  next
    case 2
    let ?q = "(x1, (y1+y2)/2)"
    have "?q ∈ W" using closed[of p ?q] assms p r 2
      by (auto simp: Rel_def)
    moreover have "p ≼ ?q ∧ ?q ≼ r ∧ ?q ≠ p ∧ ?q ≠ r"
      using 2 assms p r by (auto simp: Rel_def)
    ultimately show ?thesis by blast
  qed
qed

lemma serial: "∃q∈W. p ≼ q"
proof -
  have "(fst p, snd p + 1) ∈ W" using finite_W
    by (cases p, auto simp: finite_W)
  moreover have "p ≼ (fst p, snd p + 1)" by (auto simp: Rel_def)
  ultimately show ?thesis by blast
qed

(*────────────────── semantic truth definition ──────────────────*)

primrec eval :: "point ⇒ 'p fom ⇒ bool" where
  "eval w (Atom a)    = Val a w" |
  "eval w (Not φ)     = (¬ eval w φ)" |
  "eval w (Imp φ ψ)   = (eval w φ ⟶ eval w ψ)" |
  "eval w (F φ)       = (∃v∈W. w ≼ v ∧ eval v φ)" |
  "eval w (P φ)       = (∃v∈W. v ≼ w ∧ eval v φ)" |
  "eval w (G φ)       = (∀v∈W. w ≼ v ⟶ eval v φ)" |
  "eval w (H φ)       = (∀v∈W. v ≼ w ⟶ eval v φ)"

abbreviation valid  ("⊨ _" [55] 55) where
  "⊨ φ ≡ (∀w∈W. eval w φ)"

end  ― ‹locale Finite_Minkowski›

(*─────────────────────────────────────────────────────────────────────────*)
section ‹Model‑finding with Nitpick (example)›

text ‹Show that the axiom ‹φ ⟶ G (P φ)› (named GP) is *independent* of
      the rest.›

lemma independence_GP:
  obtains W Val
  where "finite (W::point set)"
        "¬ (∀w∈W. Finite_Minkowski.eval W Val w
               (Imp (Atom 0) (G (P (Atom 0)))))"
proof -
  (* let Nitpick build a 2‑point counter‑model *)
  nitpick[satisfy, expect = genuine,
          card point = 2,
          format = 2]
  (* Nitpick prints a concrete W, Rel, Val that works;
     the ‘expect=genuine’ option makes the lemma succeed only if such
     a model exists. *)
  by blast
qed

end
