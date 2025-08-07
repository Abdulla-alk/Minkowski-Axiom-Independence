theory MinkowskiTheoremProving
  imports Main
begin

section \<open>Formula syntax\<close>
datatype ('\<alpha>) fom =
    Atom '\<alpha>
  | Imp  "('\<alpha>) fom" "('\<alpha>) fom"         (infixr "\<rightarrow>" 25)
  | Not  "('\<alpha>) fom"                    ("\<not> _" [40] 40)
  | G    "('\<alpha>) fom"                    ("G _" [55] 55)
  | H    "('\<alpha>) fom"                    ("H _" [55] 55)
  | F    "('\<alpha>) fom"                    ("F _" [55] 55)
  | P    "('\<alpha>) fom"                    ("P _" [55] 55)

abbreviation Or  (infixr "\<or>" 30) where
  "\<phi> \<or> \<psi> \<equiv> Imp (Not \<phi>) \<psi>"

abbreviation And (infixr "\<and>" 25) where
  "\<phi> \<and> \<psi> \<equiv> Not (Imp \<phi> (Not \<psi>))"

section \<open>Hilbert calculus: axioms I–III\<close>
inductive provable :: "('\<alpha>) fom \<Rightarrow> bool"  ("\<turnstile> _" 55) where
  (* I.  Propositional K + distribution of G *)
  K1: "\<turnstile> (\<phi>           \<rightarrow> (\<psi> \<rightarrow> \<phi>))" |
  K2: "\<turnstile> ((\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>)))" |
  K3: "\<turnstile> ((\<not>\<psi> \<rightarrow> \<not>\<phi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>))" |
  GK: "\<turnstile> (G (\<phi> \<rightarrow> \<psi>) \<rightarrow> (G \<phi> \<rightarrow> G \<psi>))" |

  (* II.  Basic temporal principles *)
  GP: "\<turnstile> (\<phi> \<rightarrow> G (P \<phi>))" |
  HF: "\<turnstile> (\<phi> \<rightarrow> H (F \<phi>))" |

  (* III.  Transitive, dense, serial frame schemes *)
  G_trans:  "\<turnstile> (G \<phi> \<rightarrow> G (G \<phi>))" |          \<comment> \<open>Gp \<rightarrow> GGp\<close>
  G_dense:  "\<turnstile> (G (G \<phi>) \<rightarrow> G \<phi>)" |          \<comment> \<open>GGp \<rightarrow> Gp\<close>
  F_serial: "\<turnstile> F (\<phi> \<or> \<not>\<phi>)" |               \<comment> \<open>F\<top> (seriality)\<close>

  (* Inference rule *)
  MP: "\<turnstile> (\<phi> \<rightarrow> \<psi>) \<Longrightarrow> \<turnstile> \<phi> \<Longrightarrow> \<turnstile> \<psi>"

declare K1[intro] K2[intro] K3[intro] MP[intro]

text \<open>From this point on every theorem is derived syntactically from the
      nine axiom‑schemes above using Modus Ponens.\<close>

lemma provable_simple: "\<turnstile> (\<phi> \<rightarrow> \<phi>)"
  by (meson K1 K2 MP)
  \<comment> \<open>`meson` builds a Hilbert proof from the three propositional axioms
      and modus ponens; Isabelle checks it in the kernel.\<close>

end
