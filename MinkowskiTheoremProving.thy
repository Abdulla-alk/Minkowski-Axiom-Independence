theory MinkowskiTheoremProving
  imports Main
begin

section ‹Formula syntax›
datatype ('α) fom =
    Atom 'α
  | Imp  "('α) fom" "('α) fom"         (infixr "→" 25)
  | Not  "('α) fom"                    ("¬ _" [40] 40)
  | G    "('α) fom"                    ("G _" [55] 55)
  | H    "('α) fom"                    ("H _" [55] 55)
  | F    "('α) fom"                    ("F _" [55] 55)
  | P    "('α) fom"                    ("P _" [55] 55)

abbreviation Or  (infixr "∨" 30) where
  "φ ∨ ψ ≡ Imp (Not φ) ψ"

abbreviation And (infixr "∧" 25) where
  "φ ∧ ψ ≡ Not (Imp φ (Not ψ))"

abbreviation Iff (infixr "↔" 25) where
  "φ ↔ ψ ≡ (φ → ψ) ∧ (ψ → φ)"

section ‹Relativisation machinery›
definition hash :: "'α fom ⇒ 'α fom"  ("# _" [58] 57) where
  "# φ ≡ (¬ φ) ∧ (¬ F φ) ∧ (¬ P φ)"

primrec rel :: "'α fom ⇒ 'α fom ⇒ 'α fom"  (infix "▸" 56) where
  "rel (Atom a)    g = (g ∧ Atom a)" |
  "rel (Not φ)     g = (g ∧ Not (rel φ g))" |
  "rel (Imp φ ψ)   g = (g ∧ Imp (rel φ g) (rel ψ g))" |
  "rel (F  φ)      g = (g ∧ F (rel φ g))" |
  "rel (P  φ)      g = (g ∧ P (rel φ g))" |
  "rel (G  φ)      g = (g ∧ G (Imp g (rel φ g)))" |
  "rel (H  φ)      g = (g ∧ H (Imp g (rel φ g)))"

abbreviation half_arrow  (infix "⊩" 55) where
  "φ ⊩ g ≡ rel φ g"

section ‹Up-arrow connective›
text ‹Define ↑(p,q) ≡ F p ∧ F q ∧ G ¬(F p ∧ F q).›
definition Up :: "'α fom ⇒ 'α fom ⇒ 'α fom" where
  "Up p q ≡ (F p ∧ F q) ∧ G (¬ (F p ∧ F q))"

notation Up (infix "↑" 55)

section ‹Hilbert calculus: axioms I–III + plain confluence›
inductive provable :: "('α) fom ⇒ bool"  ("⊢ _" 55) where
  (* I.  Propositional K + distribution of G *)
  K1: "⊢ (φ           → (ψ → φ))" |
  K2: "⊢ ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))" |
  K3: "⊢ ((¬ψ → ¬φ) → (φ → ψ))" |
  GK: "⊢ (G (φ → ψ) → (G φ → G ψ))" |

  (* II.  Basic temporal principles *)
  GP: "⊢ (φ → G (P φ))" |
  HF: "⊢ (φ → H (F φ))" |

  (* III.  Transitive, dense, serial frame schemes *)
  G_trans:  "⊢ (G φ → G (G φ))" |
  G_dense:  "⊢ (G (G φ) → G φ)" |
  F_serial: "⊢ F (φ ∨ ¬φ)" |

  (* IV.  Plain confluence (no relativisation) *)
  Confl_plain:
    "⊢ (P (F (q ∧ F r)) ↔ F (P q ∧ P r))" |
  (* V.  Lightlines are linear *)
  Lightline_linear:
    "⊢ (((p ↑ # p) ∧ (F (q ∧ # p) ∧ F (r ∧ # p)))
        → F (((q ∧ F (r ∧ # p)) ∨ (q ∧ r ∧ # p)) ∨ (r ∧ F (q ∧ # p))))" |


  (* Inference rule *)
  MP: "⊢ (φ → ψ) ⟹ ⊢ φ ⟹ ⊢ ψ"

declare K1[intro] K2[intro] K3[intro] MP[intro]

text ‹From this point on every theorem is derived syntactically from the
      axiom-schemes above using Modus Ponens.›

(* tiny sanity check *)
lemma provable_simple: "⊢ (r → r)"
  by (meson K1 K2 MP)

(* relativisation sanity: g ∧ … ⇒ g *)
lemma rel_implies_guard: "⊢ ((φ ⊩ g) → g)"
  by (meson K1 K2 K3 MP)

(* up-arrow sanity: immediate consequences *)
lemma up_implies_Fp: "⊢ ((p ↑ q) →  p)"
  unfolding Up_def by (meson K1 K2 K3 MP)

lemma up_implies_Fq: "⊢ ((p ↑ q) → F q)"
  unfolding Up_def by (meson K1 K2 K3 MP)

lemma up_implies_no_joint_eventually: "⊢ ((p ↑ q) → G (¬ (F p ∧ F q)))"
  unfolding Up_def by (meson K1 K2 K3 MP)

(* placeholder to test whether the relativised confluence follows *)
lemma Confl_rel_attempt:
  "⊢ (P (F (q ∧ F r)) ↔ F (P q ∧ P r)) ⊩ (# p)"
  oops

end
