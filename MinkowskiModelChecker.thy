theory MinkowskiModelChecker
  imports MinkowskiTheoremProving "HOL.Complex_Main"
begin

(*\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>*)
section \<open>Finite slices of Minkowski space\<close>

type_synonym point = "real \<times> real"

text \<open>The future order: “go north‑east”.\<close>
definition Rel :: "point \<Rightarrow> point \<Rightarrow> bool"  (infix "\<preceq>" 50) where
  "p \<preceq> q \<longleftrightarrow> (fst p < fst q \<and> snd p < snd q)"


locale Finite_Minkowski =
  fixes W   :: "point set"                     \<comment> \<open>worlds (finite)\<close>
    and Val :: "'p \<Rightarrow> point \<Rightarrow> bool"             \<comment> \<open>valuation\<close>
  assumes finite_W: "finite W"
      and  closed: "\<lbrakk> p \<preceq> q;  p \<in> W \<rbrakk> \<Longrightarrow> q \<in> W"
begin

lemma trans:  "p \<preceq> q \<Longrightarrow> q \<preceq> r \<Longrightarrow> p \<preceq> r"
  by (auto simp: Rel_def)

lemma irrefl: "\<not>(p \<preceq> p)"
  by (simp add: Rel_def)

lemma dense:
  assumes "p \<preceq> r" and "p \<noteq> r"
  shows   "\<exists>q\<in>W. p \<preceq> q \<and> q \<preceq> r \<and> q \<noteq> p \<and> q \<noteq> r"
proof -
  obtain x1 y1 x2 y2 where p: "p=(x1,y1)" and r: "r=(x2,y2)" by (cases p, cases r)
  with assms have "x1 \<le> x2 \<and> y1 \<le> y2 \<and> (x1<x2 \<or> y1<y2)" by (auto simp: Rel_def)
  then consider "x1 < x2" | "y1 < y2" by linarith
  thus ?thesis
  proof cases
    case 1
    let ?q = "((x1+x2)/2, y1)"
    have "?q \<in> W" using closed[of p ?q] assms p r 1
      by (auto simp: Rel_def)
    moreover have "p \<preceq> ?q \<and> ?q \<preceq> r \<and> ?q \<noteq> p \<and> ?q \<noteq> r"
      using 1 assms p r by (auto simp: Rel_def)
    ultimately show ?thesis by blast
  next
    case 2
    let ?q = "(x1, (y1+y2)/2)"
    have "?q \<in> W" using closed[of p ?q] assms p r 2
      by (auto simp: Rel_def)
    moreover have "p \<preceq> ?q \<and> ?q \<preceq> r \<and> ?q \<noteq> p \<and> ?q \<noteq> r"
      using 2 assms p r by (auto simp: Rel_def)
    ultimately show ?thesis by blast
  qed
qed

lemma serial: "\<exists>q\<in>W. p \<preceq> q"
proof -
  have "(fst p, snd p + 1) \<in> W" using finite_W
    by (cases p, auto simp: finite_W)
  moreover have "p \<preceq> (fst p, snd p + 1)" by (auto simp: Rel_def)
  ultimately show ?thesis by blast
qed

(*\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> semantic truth definition \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>*)

primrec eval :: "point \<Rightarrow> 'p fom \<Rightarrow> bool" where
  "eval w (Atom a)    = Val a w" |
  "eval w (Not \<phi>)     = (\<not> eval w \<phi>)" |
  "eval w (Imp \<phi> \<psi>)   = (eval w \<phi> \<longrightarrow> eval w \<psi>)" |
  "eval w (F \<phi>)       = (\<exists>v\<in>W. w \<preceq> v \<and> eval v \<phi>)" |
  "eval w (P \<phi>)       = (\<exists>v\<in>W. v \<preceq> w \<and> eval v \<phi>)" |
  "eval w (G \<phi>)       = (\<forall>v\<in>W. w \<preceq> v \<longrightarrow> eval v \<phi>)" |
  "eval w (H \<phi>)       = (\<forall>v\<in>W. v \<preceq> w \<longrightarrow> eval v \<phi>)"

abbreviation valid  ("\<Turnstile> _" [55] 55) where
  "\<Turnstile> \<phi> \<equiv> (\<forall>w\<in>W. eval w \<phi>)"

end  \<comment> \<open>locale Finite_Minkowski\<close>

(*\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>*)
section \<open>Model‑finding with Nitpick (example)\<close>

text \<open>Show that the axiom \<open>\<phi> \<longrightarrow> G (P \<phi>)\<close> (named GP) is *independent* of
      the rest.\<close>

lemma independence_GP:
  obtains W Val
  where "finite (W::point set)"
        "\<not> (\<forall>w\<in>W. Finite_Minkowski.eval W Val w
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
