theory FibFacts
  imports "HOL-Number_Theory.Fib" HOL.Orderings 
begin


(*An expansion of Fib.thy: https://isabelle.in.tum.de/library/HOL/HOL-Number_Theory/Fib.html*)



(* TO DO:

(1) Fix index changing  issues on lines  199, 203, 319

(2) Fix issue of showing Max is an element of set it is Max of!  (Lines: 665 and 674)

(3) Sorry's on lines 678 and 703 correspond to the need for a lemma stating:
the sum of nonconsectuive fibs is strictly bounded by Fib_{max summing set + 1}
However, I don't know how to state this because I don't feel very comfortable working with Max.

(4) Do we have a floor function?  I want it for line 137 to prove another result.  
It seems HOL/Archimedean_Field.thy does but I don't understand how it works:
https://isabelle.in.tum.de/library/HOL/HOL/Archimedean_Field.html


 Total sorry count =  7
 
 Can you help with this?
 Sorry by index change: 199, 203, 319
 Sorry by Max is in set: 665 and 674

 Can you state the relevant lemma for these?
 Other sorrys: 678 and 703

*)


(* Manuel:

     (1) There's various ways to do this, but the one that basically always works is the
         rule sum.reindex_bij_witness, which allows you to simply specify the reindexing function
         and its inverse, at which point "auto" can usually do the rest. See below.

     (2) There's a theorem called "Max_in" that does exactly that. You can find it using
         the "find_theorems" command or the "find_theorems" panel in Isabelle/JEdit. You will
         of course have to prove that the set is finite and nonempty.

     (3) Taken care of below (one general version that I ended up not using because it wasn't
         quite suitable for the case you need, one simpler one specifically tailored to your use
         case).

     (4) Yes, we do have a floor function and it is indeed the one you find.
         What is your problem with it exactly? Note however that for your purpose, the "div"
         operator (integer division, always rounds down) is more convenient.
         Even better though, in many cases, is to avoid floor/div entirely (see below).
*)




(*begin on page 21*)

lemma Exercise6a: "(\<Sum>k \<in> {..n}. fib k) = fib (n+2) - 1"     (*Also exercise 7 of Andrews*)
  (* Manuel: this goes through with induction-auto *)
  by (induction n) auto



lemma Exercise8_Andrews: "(\<Sum>k \<in> {1..n}. fib (2*k-1)) = fib (2*n)"
  by(induct n rule: fib.induct, simp_all)


lemma Exercise9_Andrews: "(\<Sum>k \<in> {..n}. fib (2*k)) = fib (2*n+1) - 1"
  by(induct n rule: fib.induct, simp_all, simp add: numeral_3_eq_3)

fun gen_fib :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a :: monoid_add" where
  "gen_fib a b n = (if n = 0 then a else if n = 1 then b else gen_fib b (a + b) (n - 1))"

lemmas [simp del] = gen_fib.simps

lemma gen_fib_0 [simp]: "gen_fib a b 0 = a"
  and gen_fib_1 [simp]: "gen_fib a b 1 = b"
  by (subst gen_fib.simps; simp; fail)+

lemma gen_fib_rec: "n > 0 \<Longrightarrow> gen_fib a b n = gen_fib b (a + b) (n - 1)"
  by (cases n) (auto simp: gen_fib.simps)

lemma gen_fib_Suc [simp]: "gen_fib a b (Suc n) = gen_fib b (a + b) n"
  by (subst gen_fib_rec) auto

lemma gen_fib_of_nat: "gen_fib (of_nat a) (of_nat b) n = of_nat (gen_fib a b n)"
  by (induction a b n rule: gen_fib.induct) (auto simp: gen_fib.simps)

lemma fib_conv_gen_fib_strong: "gen_fib (fib n) (fib (n + 1)) m = fib (n + m)"
proof (induction m arbitrary: n)
  case (Suc m n)
  show ?case
    using Suc.IH[of "Suc n"] by (auto simp: gen_fib_rec add_ac)
qed auto

lemma fib_conv_gen_fib [code_abbrev]: "fib n = nat (gen_fib 0 (1 :: int) n)"
  using fib_conv_gen_fib_strong[of 0 n] gen_fib_of_nat[of 0 1 n, where ?'a = int] by simp

lemma eval_fib_numeral [simp]:
  "numeral n \<le> (100 :: nat) \<Longrightarrow> fib (numeral n) = nat (gen_fib 0 (1 :: int) (numeral n))"
  by (rule fib_conv_gen_fib)

lemma eval_gen_fib [simp]:
  "gen_fib 0 x (numeral (Num.Bit0 n)) =
   gen_fib x x (pred_numeral (Num.Bit0 n))"
  "gen_fib 0 x (numeral (Num.Bit1 n)) =
   gen_fib x x (pred_numeral (Num.Bit1 n))"
  "gen_fib x 0 (numeral (Num.Bit0 n)) =
   gen_fib 0 x (pred_numeral (Num.Bit0 n))"
  "gen_fib x 0 (numeral (Num.Bit1 n)) =
   gen_fib 0 x (pred_numeral (Num.Bit1 n))"
  "gen_fib 1 1 (numeral (Num.Bit0 n)) =
   gen_fib 1 2 (pred_numeral (Num.Bit0 n))"
  "gen_fib 1 1 (numeral (Num.Bit1 n)) =
   gen_fib 1 2 (pred_numeral (Num.Bit1 n))"
  "gen_fib 1 (numeral b) (numeral (Num.Bit0 n)) =
   gen_fib (numeral b) (numeral (Num.inc b)) (pred_numeral (Num.Bit0 n))"
  "gen_fib (numeral a) 1 (numeral (Num.Bit0 n)) =
   gen_fib 1 (numeral (Num.inc a)) (pred_numeral (Num.Bit0 n))"  
  "gen_fib 1 (numeral b) (numeral (Num.Bit1 n)) =
   gen_fib (numeral b) (numeral (Num.inc b)) (pred_numeral (Num.Bit1 n))"
  "gen_fib (numeral a) 1 (numeral (Num.Bit1 n)) =
   gen_fib 1 (numeral (Num.inc a)) (pred_numeral (Num.Bit1 n))"  
  "gen_fib (numeral a) (numeral b) (numeral (Num.Bit0 n)) =
   gen_fib (numeral b) (numeral (a + b)) (pred_numeral (Num.Bit0 n))"
  "gen_fib (numeral a) (numeral b) (numeral (Num.Bit1 n)) =
   gen_fib (numeral b) (numeral (a + b)) (pred_numeral (Num.Bit1 n))"
  by (subst gen_fib_rec; simp add: add_One add_One_commute)+

lemma fib_ge_Suc_0: "fib n \<ge> Suc 0 \<longleftrightarrow> n > 0"
  by (metis Fib.fib0 Suc_le_eq bot_nat_0.not_eq_extremum fib_neq_0_nat)

lemma Exercise6b: "(\<Sum>k \<in> {..n}. fib (2*k)) = fib (2*n+1) - 1"
proof(induction n)
  show "(\<Sum>k\<le>0. fib (2 * k)) = fib (2 * 0 + 1) - 1"
    by simp
next 
  fix n
  assume induction_hypothesis: "(\<Sum>k\<le>n. fib (2 * k)) = fib (2 * n + 1) - 1"
  have "(\<Sum>k\<le>Suc n. fib (2 * k)) = (\<Sum>k\<le> n. fib (2 * k)) + fib (2*n +2)"
    by simp
  also have "... = fib (2 * n + 1) - 1 + fib (2*n +2)"
    using induction_hypothesis by simp
  also have "... = fib (2 * n + 1) + fib (2 * n + 2) - 1"
    by (rule add_diff_assoc2) (use fib_ge_Suc_0[of "2*n+1"] in auto)
  also have "... = fib (2 * n + 3) - 1 "
    by (simp add: add.commute numeral_3_eq_3)
  also have "... = fib (2 * Suc n + 1) - 1"
    by (simp add: numeral_3_eq_3)
  finally show "(\<Sum>k\<le>Suc n. fib (2 * k)) = fib (2 * Suc n + 1) - 1" .
qed

lemma Exercise6c: "(\<Sum>k=1..n. fib (2*k-1)) = fib (2*n)"
  by (induct n rule: fib.induct) simp_all

lemma Exercise6d: "(\<Sum>k\<le>n. fib(k)*fib(k)) = fib(n)*fib(n+1)"
  by (metis Suc_eq_plus1 fib_mult_eq_sum_nat mult.commute)
(*Already solved as "fib_mult_eq_sum_nat" but I prefer this representation and this order of presentation.*)







(* Manuel: why not simply like this? *)
lemma Exercise6e: "fib(n)*fib(n+2) = (fib(n+1)*fib(n+1))+(-1)^(n+1)"
  by (induction n rule: fib.induct) (auto simp: algebra_simps)

(* Manuel: by the way, you can also write fib(2*n) ^ 2 or fib(2*n)² *)
lemma Exercise11_Andrews: "(\<Sum>k \<in> {2..(2*n)}. fib(k-1)*fib(k)) = fib(2*n)*fib(2*n)"
  by(induct n rule: fib.induct, simp+, simp add: comm_semiring_class.distrib distrib_left)


lemma Exercise12_Andrews: "(\<Sum>k=2..2*n+1. fib(k-1)*fib(k)) = fib(2*n+1)*fib(2*n+1)-1"
proof - 
  have "(\<Sum>k \<in> {2..(2*n+1)}. fib(k-1)*fib(k)) = (\<Sum>k \<in> {2..(2*n)}. fib(k-1)*fib(k)) + fib(2*n)*fib(2*n+1)"
    by simp
  also have "... = (fib(2*n)*fib(2*n)) + fib(2*n)*fib(2*n+1)"
    using Exercise11_Andrews by presburger
  also have "... = fib(2*n)*(fib(2*n) + fib(2*n+1))"
    by (simp add: distrib_left)
  also have "... = fib(2*n)*fib(2*n+2)"
    by simp
  also have "... = (-1::int)^(2*n+1::nat) + fib(2*n+1)*fib(2*n+1)"
    by (smt (verit, best) Exercise6e add.assoc add_diff_cancel_right' nat_1_add_1) 
  also have "... = fib(2*n+1)*fib(2*n+1) - 1"
    by (smt (z3) Suc_eq_plus1 \<open>int (fib (2 * n) * fib (2 * n + 2)) = (- 1) ^ (2 * n + 1) + int (fib (2 * n + 1) * fib (2 * n + 1))\<close> add_2_eq_Suc' fib_Cassini_nat mult.commute of_nat_Suc power2_eq_square power_minus1_odd)
  then show ?thesis
    using calculation by auto    
qed




    
    

lemma Pascals_Identity: "(n choose k)+(n choose (k+1)) = ((n+1) choose (k+1))"
  by simp


lemma fib_rec: "n \<ge> 2 \<Longrightarrow> fib n = fib (n - 1) + fib (n - 2)"
  by (auto simp: eval_nat_numeral less_eq_nat.simps split: nat.splits)

(*Consider proving exercise 13 of 3.1 from Andrews*)
(* https://proofwiki.org/wiki/Fibonacci_Number_as_Sum_of_Binomial_Coefficients *)

lemma fib_conv_sum_binomial:
  "fib (2 * n + 1) = (\<Sum>k\<le>n. ((2*n - k) choose k))"
  "fib (2 * n + 2) = (\<Sum>k\<le>n. ((2*n - k + 1) choose k))"
proof -
  have "fib (2 * n + 1) = (\<Sum>k\<le>n. ((2*n - k) choose k)) \<and>
        fib (2 * n + 2) = (\<Sum>k\<le>n. ((2*n - k + 1) choose k))"
  proof (induction n)
    case 0
    thus ?case by auto
  next
    case (Suc n)
    have "(\<Sum>k\<le>Suc n. ((2*Suc n - k) choose k)) = Suc (\<Sum>i\<le>n. Suc (2 * n - i) choose Suc i)"
      by (subst sum.atMost_Suc_shift) (auto simp: Suc_diff_le)
    also have "\<dots> = (\<Sum>i\<le>n. (2 * n - i) choose i) + Suc (\<Sum>i\<le>n. (2 * n - i) choose Suc i)"
      by (auto simp: sum.distrib)
    also have "Suc (\<Sum>i\<le>n. (2 * n - i) choose Suc i) = (\<Sum>i\<le>Suc n. (2 * Suc n - i - 1) choose i)"
      by (subst sum.atMost_Suc_shift) (auto simp: Suc_diff_le)
    also have "\<dots> = (\<Sum>i\<le>n. (2*n - i + 1) choose i)"
      by (simp add: Suc_diff_le)
    also have "(\<Sum>i\<le>n. (2 * n - i) choose i) + \<dots> = fib (2 * n + 3)"
      using Suc.IH by (simp add: fib_rec add_ac)
    finally have 1: "fib (2 * n + 3) = (\<Sum>k\<le>Suc n. 2 * Suc n - k choose k)" ..

    have "(\<Sum>k\<le>Suc n. ((2*Suc n - k + 1) choose k)) = Suc (\<Sum>i\<le>n. Suc (2 * n - i + 1) choose Suc i)"
      by (subst sum.atMost_Suc_shift) (auto simp: Suc_diff_le)
    also have "\<dots> = (\<Sum>i\<le>n. (2 * n - i + 1) choose i) + Suc (\<Sum>i\<le>n. (2 * n - i + 1) choose Suc i)"
      by (auto simp: sum.distrib)
    also have "Suc (\<Sum>i\<le>n. (2 * n - i + 1) choose Suc i) = (\<Sum>i\<le>Suc n. (2 * Suc n - i) choose i)"
      by (subst sum.atMost_Suc_shift) (auto simp: Suc_diff_le)
    also have "\<dots> = fib (2 * n + 3)"
      using 1 by simp
    finally have 2: "fib (2 * n + 4) = (\<Sum>k\<le>Suc n. 2 * Suc n - k + 1 choose k)"
      using Suc.IH fib_rec[of "2*n+4"] by (simp add: algebra_simps)

    have "2 * Suc n + 1 = 2 * n + 3" and "2 * Suc n + 2 = 2 * n + 4"
      by auto
    with 1 and 2 show ?case
      by metis
  qed
  thus "fib (2 * n + 1) = (\<Sum>k\<le>n. ((2*n - k) choose k))"
       "fib (2 * n + 2) = (\<Sum>k\<le>n. ((2*n - k + 1) choose k))"
    by blast+  
qed



lemma fib_conv_sum_binomial':
  assumes "n > 0"
  shows   "fib n = (\<Sum>k\<le>(n-1) div 2. ((n - k - 1) choose k))"
  using assms fib_conv_sum_binomial[of "(n - 1) div 2"]
proof (cases "even n")
  case True
  hence "even (n - 2)" "n \<ge> 2"
    using assms by auto
  then obtain n' where "n - 2 = 2 * n'"
    by blast
  hence "n = 2 * n' + 2"
    using \<open>n \<ge> 2\<close> by simp
  with fib_conv_sum_binomial(2)[of n'] show ?thesis
    by (simp add: Suc_diff_le)
next
  case False
  then obtain n' where "n = 2 * n' + 1"
    by (elim oddE)
  with fib_conv_sum_binomial(1)[of n'] show ?thesis
    by (simp add: Suc_diff_le)
qed


lemma Exercise8a: "\<forall>m. (\<Sum>k \<in> {0..n}. (n choose k)*fib(m+k)) = fib(2*n+m)" 
proof(rule allI, induction n)
  fix m 
  show "(\<Sum>k = 0..0. (0 choose k) * fib (m + k)) = fib (2 * 0 + m)"
    by simp
next
  fix m n  
  assume induction_hypothesis: "(\<And>j. (\<Sum>k = 0..n. (n choose k) * fib (j + k)) = fib (2 * n + j))"

  show "(\<Sum>k = 0..Suc n. (Suc n choose k) * fib (m + k)) = fib (2 * Suc n + m)"
  proof(cases "n \<le> 2",simp)  (*We later will use the fact that n > 2 so we need to resolve these cases*)
    assume "n \<le> 2" 
    show "(\<Sum>k = 0..n. (Suc n choose k) * fib (m + k)) + fib (Suc (m + n)) = fib (Suc (2 * n + m)) + fib (2 * n + m)"
    proof(cases "n=0",simp)
      assume "n \<noteq> 0"  show ?thesis
      proof(cases "n=1",simp)
        assume "n \<noteq> 1" then have "n = 2"   (*Oddly enough, it is not enough to cover the case when n=1 to get it must be 2, we must also re-visit the case when n=0, why?!*)
          by (metis One_nat_def \<open>n \<le> 2\<close> \<open>n \<noteq> 0\<close> le_neq_implies_less less_2_cases_iff)
        have "(\<Sum>k = 0..n. (Suc n choose k) * fib (m + k)) + fib (Suc (m + n))   = 
               (((Suc 2 choose 0) * fib (m + 0)) + ((Suc n choose 1) * fib (m + 1)) + ((Suc n choose 2) * fib (m + 2))) + fib (Suc (m + n)) "
          by (metis (no_types, lifting) One_nat_def Suc_1 \<open>n = 2\<close> add.assoc add_left_cancel le_add1 plus_1_eq_Suc sum.atLeast0_atMost_Suc sum.atLeast_Suc_atMost sum.ub_add_nat)
        also have "... = (fib (m) + (3 * fib (m + 1)) + (3 * fib (m + 2))) + fib (Suc (m + n))"
          using \<open>n = 2\<close> One_nat_def Suc_1 binomial_Suc_n numeral_3_eq_3 by (simp, presburger)
        also have "... = ((fib(m) + fib(m+1)) + fib(m+1) + (fib(m+1) + fib(m+2)) + fib(m+2) + fib(m+2)) + fib (Suc (m + n)) "
          by simp
        also have "... = ((fib(m+2) + fib(m+1)) + (fib(m+3) + fib(m+2)) + fib(m+2)) + fib (Suc (m + n)) "
          by (simp add: numeral_3_eq_3)
        also have "... = ((fib(m+3)) + (fib(m+4)) + fib(m+2)) + fib (Suc (m + n))"
          by (simp add: numeral_Bit0)
        also have "... = (fib(m+5)  + fib(m+2)) + fib(m+3)"
          by (smt (z3) Fib.fib2 Suc_nat_number_of_add \<open>n = 2\<close> add.commute semiring_norm(2) semiring_norm(5) semiring_norm(8))
        also have "... = fib(m+6)"
          by (simp add: numeral_eq_Suc)
        also have "... = fib (Suc (2 * n + m)) + fib (2 * n + m)"
          by (simp add: \<open>n = 2\<close> eval_nat_numeral(3) numeral_Bit0)
        then show ?thesis
          using calculation by presburger
      qed
    qed
  next
    assume "\<not> n \<le> 2" then have "n > 2"
      by (meson not_le)

    have index_change: "(\<Sum>k = 2..n. ((n+1) choose k) * fib (m + k)) = (\<Sum>k = 1..(n-1). ((n+1) choose (k+1)) * fib (m + (k+1)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k+1" "\<lambda>k. k-1"]) (use \<open>n > 2\<close> in auto)

    have another_index_change: "(\<Sum>k = 0..(n-2). ((n choose (k+1)) * fib (m + (k+1)))) = 
                                (\<Sum>k = 1..(n-1). ((n choose k) * fib (m + k)))"
      by (rule sum.reindex_bij_witness[of _ "\<lambda>k. k-1" "\<lambda>k. k+1"]) (use \<open>n > 2\<close> in auto)

    have "(\<Sum>k = 0..Suc n. (Suc n choose k) * fib (m + k)) = 
          (\<Sum>k = 0..n. ((n+1) choose k) * fib (m + k)) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by simp
    also have "... =  ((n+1) choose 0) * fib (m + 0) + (\<Sum>k = 1..n. ((n+1) choose k) * fib (m + k)) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by (simp add: sum.atLeast_Suc_atMost) 
    also have "... =  ((n+1) choose 0) * fib (m + 0) + ((n+1) choose 1) * fib (m + 1) + (\<Sum>k = 2..n. ((n+1) choose k) * fib (m + k)) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by (smt (verit, ccfv_threshold) Nat.lessE Suc_1 \<open>2 < n\<close> add.assoc le_add1 plus_1_eq_Suc sum.atLeast_Suc_atMost)
    also have "... =  ((n+1) choose 0) * fib (m + 0) + ((n+1) choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-1). ((n+1) choose (k+1)) * fib (m + (k+1))) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      using index_change by presburger
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-1). ((n+1) choose (k+1)) * fib (m + (k+1))) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by force    
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n+1) choose (k+1)) * fib (m + (k+1))) + 
                      ((n+1) choose (n)) * fib (m + n) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by (smt (verit, del_insts) Nat.add_diff_assoc2 \<open>2 < n\<close> add_diff_cancel_right' add_lessD1 le_add2 le_add_diff_inverse nat_1_add_1 nat_less_le plus_1_eq_Suc sum.cl_ivl_Suc)
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n choose (k+1)) + (n choose k)) * fib (m + (k+1))) + 
                      ((n+1) choose n) * fib (m + n) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by (metis Suc_eq_plus1 add.commute binomial_Suc_Suc)
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n choose (k+1)) + (n choose k)) * fib (m + (k+1))) + 
                      ((n choose (n-1)) + (n choose n)) * fib (m + n) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      using \<open>\<not> n \<le> 2\<close> binomial_symmetric by force
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n choose (k+1)) * fib (m + (k+1))) + ((n choose k)  * fib (m + (k+1)))   ) + 
                      (n choose (n-1)) * fib (m + n) + (n choose n) * fib (m + n) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      using add_mult_distrib by presburger
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n choose (k+1)) * fib (m + (k+1)))) +
                                                                                                        (\<Sum>k = 1..(n-2). ((n choose k)  * fib (m + (k+1)))   ) + 
                      (n choose (n-1)) * fib (m + n) + (n choose n) * fib (m + n) + (((n+1) choose (n+1)) * fib (m + (n+1)))"
      by (simp add: sum.distrib)
    also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) + (n choose 1) * fib (m + 1) + (\<Sum>k = 1..(n-2). ((n choose (k+1)) * fib (m + (k+1)))) +
                                                                                                        (\<Sum>k = 1..(n-1). ((n choose k)  * fib (m + (k+1)))   ) + 
                      (n choose n) * fib (m + n) + ((n choose n) * fib (m + (n+1)))"
      using binomial_n_n by (smt (verit, ccfv_threshold) Nat.add_diff_assoc2 \<open>2 < n\<close> add_diff_cancel_right' add_lessD1 le_add2 le_add_diff_inverse nat_1_add_1 nat_less_le plus_1_eq_Suc sum.cl_ivl_Suc)
   also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) +  (\<Sum>k = 0..(n-2). ((n choose (k+1)) * fib (m + (k+1)))) +
                                                                                                        (\<Sum>k = 1..(n-1). ((n choose k)  * fib (m + (k+1)))   ) + 
                      (n choose n) * fib (m + n) + ((n choose n) * fib (m + (n+1)))"
     by (simp add: sum.atLeast_Suc_atMost)
   also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) +  
                   ((\<Sum>k = 1..(n-1). ((n choose k) * fib (m + k))) + (n choose n) * fib (m + n)) +
                    (\<Sum>k = 1..(n-1). ((n choose k)  * fib (m + (k+1))))  + ((n choose n) * fib (m + (n+1)))"
     using another_index_change by presburger
   also have "... =  (n choose 0) * fib (m) + (n choose 0)* fib (m + 1) +  
                    (\<Sum>k = 1..n. ((n choose k) * fib (m + k))) + 
                    (\<Sum>k = 1..(n-1). ((n choose k)  * fib (m + (k+1))))  + ((n choose n) * fib (m + (n+1)))"
     by (metis (no_types, lifting) One_nat_def Suc_pred \<open>\<not> n \<le> 2\<close> less_2_cases_iff less_Suc0 nat_less_le neq0_conv sum.cl_ivl_Suc)
   also have "... =  (n choose 0) * (fib(m) +  fib (m + 1)) +  
                    (\<Sum>k = 1..n. ((n choose k) * fib (m + k))) + 
                   ((\<Sum>k = 1..(n-1). ((n choose k)  * fib (m + (k+1))))  + ((n choose n) * fib (m + (n+1))))"
      by fastforce
   also have "... =  (n choose 0) * (fib(m) +  fib (m + 1)) +  
                    (\<Sum>k = 1..n. ((n choose k) * fib (m + k))) + 
                    (\<Sum>k = 1..n. ((n choose k)  * fib (m + (k+1))))"
     by (smt (z3) One_nat_def Suc_pred 
        \<open>(n choose 0) * fib m + (n choose 0) * fib (m + 1) + ((\<Sum>k = 1..n - 1. (n choose k) * fib (m + k)) + (n choose n) * fib (m + n)) + (\<Sum>k = 1..n - 1. (n choose k) * fib (m + (k + 1))) + (n choose n) * fib (m + (n + 1)) = (n choose 0) * fib m + (n choose 0) * fib (m + 1) + (\<Sum>k = 1..n. (n choose k) * fib (m + k)) + (\<Sum>k = 1..n - 1. (n choose k) * fib (m + (k + 1))) + (n choose n) * fib (m + (n + 1))\<close> 
        \<open>2 < n\<close> add_gr_0 add_left_imp_eq add_right_imp_eq binomial_n_n fib_neq_0_nat lambda_one less_imp_le_nat neq0_conv not_numeral_le_zero sum.cl_ivl_Suc)
   also have "... =  (n choose 0) * (fib(m) +  fib (m + 1)) +  
                    (\<Sum>k = 1..n. ((n choose k) * fib (m + k)) + ((n choose k) * fib (m + (k+1))))"
     by (simp add: sum.distrib)
   also have "... =  (n choose 0) * (fib(m) +  fib (m + 1)) +  
                    (\<Sum>k = 1..n. (n choose k) * (fib (m + k) +  fib (m + (k+1))))"
     by (simp add: distrib_left)
   also have "... =  (n choose 0) * fib (m + 2)  +  (\<Sum>k = 1..(n). (n choose k) * (fib (m + (k+2))))"
     by (simp add: add.commute)
   also have "... =  (\<Sum>k = 0..n. (n choose k) * (fib ((m+2) + k)))"
     by (simp add: sum.atLeast_Suc_atMost)
   also have "... = fib (2*n + (m+2))"
     using induction_hypothesis by blast
   also have "... = fib (2 * Suc n + m)"
     by simp
   then show ?thesis 
     using calculation by auto
 qed
qed







lemma Exercise8b: "(\<Sum>k = 1..n. (n choose k)*fib(k)) = fib(2*n)"
proof(induction n)
  show "(\<Sum>k = 1..0. (0 choose k) * fib k) = fib (2 * 0)"
    by simp
next
  fix n
  assume induction_hypothesis: "(\<Sum>k = 1..n. (n choose k) * fib k) = fib (2 * n)"
  show "(\<Sum>k = 1..Suc n. (Suc n choose k) * fib k) = fib (2 * Suc n)"
  (* Manuel: never use something like simp/auto in an initial proof method! *)
  proof(cases "n \<le> 2")
    assume "n \<le> 2"
    (* Manuel: this pattern is a lot simpler than what you did *)
    then consider "n = 0" | "n = 1" | "n = 2"
      by linarith
    thus ?thesis
      by cases (auto simp: numeral_3_eq_3)
  next
    assume "\<not> n \<le> 2" then have "n > 2"
      by auto
    have index_shift: "(\<Sum>k = 1..n. ((n choose (k-1))* fib k  )) = (\<Sum>k = 0..(n-1). ((n choose k)* fib (k+1)  ))"
      using \<open>n > 2\<close> by (intro sum.reindex_bij_witness[of _ "\<lambda>k. k+1" "\<lambda>k. k-1"]) auto
      
    have "(\<Sum>k = 1..Suc n. (Suc n choose k) * fib k)  = (\<Sum>k = 1..n. ((n+1) choose k) * fib k) +  fib (n+1)"
      by force
    also have "... = (\<Sum>k = 1..n. ((n choose (k-1)) + (n choose k )) * fib k) +  fib (n+1)"
      by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_pred atLeastAtMost_iff binomial_Suc_Suc not_le not_less_eq_eq sum.cong)
    also have "... = (\<Sum>k = 1..n. ((n choose (k-1))* fib k + (n choose k )* fib k)  ) +  fib (n+1)"
      by (simp add: distrib_left mult.commute)
    also have "... = (\<Sum>k = 1..n. ((n choose (k-1))* fib k  )) +
                     (\<Sum>k = 1..n.  (n choose k )* fib k) +  fib (n+1)"
      by (simp add: sum.distrib)
    also have "... = (\<Sum>k = 0..(n-1). ((n choose k)* fib (k+1)  )) +
                     (\<Sum>k = 1..n.  (n choose k )* fib k) +  fib (n+1)"
      using index_shift by presburger
    also have "... =  (\<Sum>k = 0..(n-1). ((n choose k)* fib (k+1)  )) +
                      fib (2 * n) + fib(n+1)"
      using induction_hypothesis by presburger                    
    also have "... =  ((\<Sum>k = 0..(n-1). ((n choose k)* fib (1+k))) +  (n choose n)*fib(n+1)) + fib (2 * n)"
      by simp
    also have "... = ((\<Sum>k = 0..n. ((n choose k)* fib (1+k)))) + fib (2 * n)"
      by (metis (no_types, lifting) One_nat_def Suc_pred \<open>\<not> n \<le> 2\<close> add.commute le_add2 le_add_same_cancel2 nat_1_add_1 nat_less_le sum.atLeast0_atMost_Suc)
    also have "... = fib (2 * n + 1) + fib(2 * n)"
      using Exercise8a by presburger
    also have "... = fib (2 * Suc n)"
      by simp
    then show ?thesis 
      using calculation by auto
  qed
qed





  






lemma Example0_25: "fib(n)*fib(m) + fib(n+1)*fib(m+1) = fib(n+m+1)"
  using fib_add by force

(* Manuel:
     I for one find it is generally a bad idea to prove existentials when you have a constructive
     proof. You *know* what the j is here, so why are you hiding that information?
*)
lemma section1_2_exercise8:
  "\<exists>j. fib(k*n) = j*fib(n)"
proof(induct k)
  show "\<exists>j. fib (0 * n) = j * fib n"
    by simp
next
  fix k 
  assume "\<exists>j. fib (k * n) = j * fib n"
  then obtain j where j_def: "fib(k*n) = j * fib n"
    by blast
  show "\<exists>j. fib (Suc k * n) = j * fib n "
  proof(cases "n=0")
    show "n = 0 \<Longrightarrow> \<exists>j. fib (Suc k * n) = j * fib n"
      by force
  next
    assume n_nonzero: "n \<noteq> 0"
    have "fib (Suc k * n) = fib((k+1)*n)"
      using Suc_eq_plus1 by presburger
    also have "... = fib((k*n) +n)"
      by (simp add: add.commute)
    also have "... = fib(((k*n)+n) +1-1)"
      by simp
    also have "... = fib(((k*n)+(n -1)) +1)"
      using n_nonzero by force
    also have "... = (fib(k*n)*fib(n-1)) + (fib((k*n)+1)*fib((n-1)+1))"
      using Example0_25 by presburger
    also have "... = (fib(k*n)*fib(n-1)) + (fib((k*n)+1)*fib(n))"
      by (metis Suc_eq_plus1 Suc_pred \<open>fib (k * n + n + 1 - 1) = fib (k * n + (n - 1) + 1)\<close> add.left_neutral diff_Suc_1 mult_0_right neq0_conv)
    also have "... = ((j * fib n)*fib(n-1)) + (fib((k*n)+1)*fib(n))"
      by (simp add: j_def)
    also have "... = (j * fib (n-1))*fib(n) + (fib((k*n)+1)*fib(n))"
      by simp
    also have "... = (  (j * fib (n-1)) + fib((k*n)+1)  )   *fib(n)"
      by (simp add: distrib_left mult.commute)
    then show "\<exists>j. fib (Suc k * n) = j * fib n"
      by (metis calculation)
  qed
qed



(*
  Manuel: This could probably be generalised to any increasing sequence of naturals/integers.
          Or any increasing sequence that goes to infinity on a linearly-ordered type.
*)
lemma Fibonacci_sandwich: "(\<exists>j. fib(j+2) = Suc n) \<or> (\<exists> j. (fib(j+2) < Suc n ) \<and> (Suc n < fib(j+3)))"
  (*Every nonzero nat is either a fib or between two fibs*)  
proof(induct n rule: fib.induct)
  show "(\<exists>j. fib (j + 2) = Suc 0) \<or> (\<exists>j. fib (j + 2) < Suc 0 \<and> Suc 0 < fib (j + 3))"
    by (metis One_nat_def add.left_neutral fib_2)
  show "(\<exists>j. fib (j + 2) = Suc (Suc 0)) \<or> (\<exists>j. fib (j + 2) < Suc (Suc 0) \<and> Suc (Suc 0) < fib (j + 3))"
    by (metis One_nat_def Suc_1 fib_1 fib_2 fib_plus_2 plus_1_eq_Suc)
next
  show "\<And>n. (\<exists>j. fib (j + 2) = Suc (Suc n)) \<or> (\<exists>j. fib (j + 2) < Suc (Suc n) \<and> Suc (Suc n) < fib (j + 3)) \<Longrightarrow>
         (\<exists>j. fib (j + 2) = Suc n) \<or> (\<exists>j. fib (j + 2) < Suc n \<and> Suc n < fib (j + 3)) \<Longrightarrow>
         (\<exists>j. fib (j + 2) = Suc (Suc (Suc n))) \<or> (\<exists>j. fib (j + 2) < Suc (Suc (Suc n)) \<and> Suc (Suc (Suc n)) < fib (j + 3))"
  proof - 
    fix n 
    assume a1:"(\<exists>j. fib (j + 2) = Suc (Suc n)) \<or> (\<exists>j. fib (j + 2) < Suc (Suc n) \<and> Suc (Suc n) < fib (j + 3))"
    assume a2: " (\<exists>j. fib (j + 2) = Suc n) \<or> (\<exists>j. fib (j + 2) < Suc n \<and> Suc n < fib (j + 3))"
    show "(\<exists>j. fib (j + 2) = Suc (Suc (Suc n))) \<or> (\<exists>j. fib (j + 2) < Suc (Suc (Suc n)) \<and> Suc (Suc (Suc n)) < fib (j + 3))"
    proof(cases "(\<exists>j. fib (j + 2) = Suc (Suc n))")
      assume case1: "\<exists>j. fib (j + 2) = Suc (Suc n)"
      show ?thesis
      proof(cases "(\<exists>j. fib (j + 2) = Suc n)")
        assume "\<exists>j. fib (j + 2) = Suc n"
        show ?thesis
          by (metis (mono_tags, lifting) Fib.fib2 One_nat_def Suc_1 Suc_eq_plus1 Suc_lessI case1 add_Suc_shift add_gr_0 nat_add_left_cancel_less numeral_3_eq_3 zero_less_one)
      next
        assume "\<nexists>j. fib (j + 2) = Suc n"
        show ?thesis
          by (smt (z3) Fib.fib2 One_nat_def Suc_1 \<open>\<exists>j. fib (j + 2) = Suc (Suc n)\<close> add.commute add_Suc_right lessI less_add_Suc2 linorder_neqE_nat numeral_3_eq_3)
      qed
      
    next
      assume case2: "\<nexists>j. fib (j + 2) = Suc (Suc n)"
      show ?thesis
      proof(cases "(\<exists>j. fib (j + 2) = Suc n)")
        assume "\<exists>j. fib (j + 2) = Suc n"
        show ?thesis
          by (metis One_nat_def Suc_1 a1 case2 add_Suc_shift less_Suc_eq not_less_eq numeral_3_eq_3)
      next
        assume "\<nexists>j. fib (j + 2) = Suc n"
        show ?thesis
          by (metis Suc_lessI a1 add_2_eq_Suc' add_Suc_right case2 eval_nat_numeral(3) less_Suc_eq)
      qed
    qed
  qed
qed




(*
  Manuel: Again, you're hiding information here! Why not simply define a recursive function
    that computes the witness (by simply subtracting the biggest i such that fib i \<le> n)
    and then prove that it indeed yields a correct "encoding"?
*)
lemma Zeckendorf_theorem_existence: 
"\<exists>I. finite I \<and> (\<forall> a b. (a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b+1)) \<and> n = (\<Sum>(i::nat)\<in>I. fib (i+2))"
proof(induction n rule: less_induct)
  fix x 
  assume induction_hypothesis: "(\<And>y. y < x \<Longrightarrow> \<exists>I. finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> y = (\<Sum>i\<in>I. fib (i + 2)))"
  show "\<exists>I. finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
  proof(cases "x = 0") 
    show "x = 0 \<Longrightarrow> \<exists>I. finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
        by force  (*Empty sum*)
   next
     assume "x \<noteq> 0"
     show ?thesis
     proof(cases "\<exists>j. x = fib(j+2)")
       assume "\<exists>j. x = fib (j+2)"
       then obtain j where j_def: "x = fib(j+2)"
         by blast
       then have "finite {j} \<and> (\<forall>a b. a \<in> {j} \<and> b \<in> {j} \<longrightarrow> a \<noteq> b + 1) \<and> x = (\<Sum>i\<in>{j}. fib (i + 2))"
         by auto
       then show ?thesis 
         by blast
     next 
       assume "\<nexists>j. x = fib (j + 2)"
       then have "\<exists>j. fib(j+2) < x \<and> x < fib(j+3)"
         by (metis \<open>x \<noteq> 0\<close> Fibonacci_sandwich not0_implies_Suc)
       then obtain j where j_def: "fib(j+2) < x \<and> x < fib(j+3)"
         by blast
       obtain n where n_def: "n = x - fib(j+2)"
         by blast
       then have "n < fib(j+3) - fib(j+2)"
         by (metis diff_add j_def less_diff_conv less_imp_le_nat)
       then have "n < fib(j+1)"
         by (simp add: numeral_3_eq_3)
       then have "n < fib(j+2)"
         by simp
       then have "n < x"
         by (meson j_def less_trans)
       then obtain I where I_def: "finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>i\<in>I. fib (i + 2))"
         using induction_hypothesis by blast
       have "j-1 \<notin> I"   
       proof(rule ccontr,simp)
         assume "j - Suc 0 \<in> I" then have "j - 1 \<in> I"
           by auto
         then have f1:"fib((j-1)+2) \<le> n"
           by (metis I_def member_le_sum zero_le)
         then have "fib(j+1) \<le> n"
           by (metis Fib.fib1 One_nat_def Suc_1 Suc_eq_plus1 Suc_pred \<open>\<nexists>j. x = fib (j + 2)\<close> \<open>n < fib (j + 1)\<close> add_2_eq_Suc' fib_2 less_Suc0 n_def neq0_conv) 
         then show False
           using \<open>n < fib (j + 1)\<close> leD by blast
       qed
       have "j \<notin> I" 
       proof(rule ccontr,simp)
         assume "j \<in> I"
         then have f1:"fib(j+2) \<le> n"
           by (metis I_def member_le_sum zero_le)
         then show False
           using \<open>n < fib (j + 2)\<close> not_le by blast
       qed
       then have "x = n + fib(j+2)"
         by (metis diff_add j_def less_imp_le_nat n_def)
       have f1: "finite (I \<union> {j})"
         by (simp add: I_def)
       have f2: "(\<forall>a b. a \<in> (I \<union> {j}) \<and> b \<in> (I \<union> {j}) \<longrightarrow> a \<noteq> b + 1)"
       proof(rule allI,rule allI,rule impI)
         fix a b
         assume "a \<in> I \<union> {j} \<and> b \<in> I \<union> {j}"
         show "a \<noteq> b + 1"
         proof(cases "a \<in> I")
           assume "a \<in> I"
           show "a \<noteq> b + 1"
           proof(cases "b \<in> I")
             show "b \<in> I \<Longrightarrow> a \<noteq> b + 1"
               using I_def \<open>a \<in> I\<close> by blast
           next
             assume "b \<notin> I"
             then have "b = j"
               using \<open>a \<in> I \<union> {j} \<and> b \<in> I \<union> {j}\<close> by fastforce
             show "a \<noteq> b + 1"     
             proof(rule ccontr, auto)
               assume BWOC: "a = Suc b"
               have f1:"fib(a+2) \<le> n"
                 using I_def by (meson I_def \<open>a \<in> I\<close> member_le_sum zero_le)  
               have "n < fib(b+1)"
                 using \<open>b = j\<close> \<open>n < fib (j + 1)\<close> by fastforce
               then show False
                 using BWOC f1 by auto
             qed
           qed
         next
           assume "a \<notin> I"
           then have "a = j"
             using \<open>a \<in> I \<union> {j} \<and> b \<in> I \<union> {j}\<close> by blast
           show "a \<noteq> b + 1"
           proof(cases "b \<in> I")
             show "b \<in> I \<Longrightarrow> a \<noteq> b + 1"
               using \<open>a = j\<close> \<open>j - 1 \<notin> I\<close> by auto 
           next
             assume "b \<notin> I"
             then have "b = j"
               using \<open>a \<in> I \<union> {j} \<and> b \<in> I \<union> {j}\<close> by fastforce
             then show  "a \<noteq> b + 1"
               by (simp add: \<open>a = j\<close>)
           qed
         qed  
       qed         
       have f3: "x = (\<Sum>i\<in>(I \<union> {j}). fib (i + 2))"
         by (simp add: I_def \<open>j \<notin> I\<close> \<open>x = n + fib (j + 2)\<close>)
       then show ?thesis
         by (metis f1 f2)
     qed
  qed
qed

lemma sum_fib_shifted_eq_fib: "(\<Sum>i\<le>n. fib (i + 2)) + 2 = fib (n + 4)"
proof -
  have "fib (n + 4) - 1 = (\<Sum>i\<le>n+2. fib i)"
    by (subst Exercise6a) (auto simp del: fib.simps simp: eval_nat_numeral)
  also have "(\<Sum>i\<le>n+2. fib i) = (\<Sum>i\<in>{2..n+2}\<union>{0,1}. fib i)"
    by (intro sum.cong) auto
  also have "\<dots> = (\<Sum>i=2..n+2. fib i) + 1"
    by (subst sum.union_disjoint) auto
  also have "(\<Sum>i=2..n+2. fib i) = (\<Sum>i\<le>n. fib (i + 2))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. i+2" "\<lambda>i. i-2"])
       (auto simp del: fib.simps simp flip: Suc_diff_le)
  finally show ?thesis by linarith
qed

lemma fib_pos_iff: "fib n > 0 \<longleftrightarrow> n > 0"
  by (metis Fib.fib0 fib_neq_0_nat gr0I)

lemma fib_strict_mono:
  assumes "n \<ge> 3" "m < n"
  shows   "fib m < fib n"
proof -
  have "fib m \<le> fib (n - 1)"
    by (rule fib_mono) (use assms in auto)
  also have "\<dots> < fib (n - 1) + fib (n - 2)"
    using assms by (simp add: fib_pos_iff)
  also have "\<dots> = fib n"
    using assms by (subst fib_rec) auto
  finally show ?thesis .
qed

lemma fib_less_iff: 
  assumes "m \<ge> 2 \<or> n \<ge> 3"
  shows   "fib m < fib n \<longleftrightarrow> m < n"
  by (cases m n rule: linorder_cases)
     (use assms fib_strict_mono[of n m] fib_mono[of n m] in auto)

lemma fib_gt_Suc_0_iff: "fib n > Suc 0 \<longleftrightarrow> n \<ge> 3"
  using fib_less_iff[of 2 n] by auto


(* Manuel: This is the strongest inequality on non-consecutive sums of Fibonacci numbers I was
     able to derive. Unfortunately it has an ugly case split for even/odd.
     Note that I phrased it in terms of "Max (insert 0 I)" because otherwise it breaks for I = {}.
*)
lemma sum_nonconsec_fib_less_strong_aux:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I"
  shows   "(\<Sum>i\<in>I. fib i) <
             fib (Suc (Max (insert 0 I))) + (if even (Max (insert 0 I)) then 0 else 1)"
  using assms
proof (induction I rule: finite_psubset_induct)
  case (psubset I)
  define n where "n = Max (insert 0 I)"
  have [simp]: "finite I"
    by fact
  show ?case
  proof (cases "I \<subseteq> {..1}")
    case I: True
    define I' where "I' = I - {0}"
    have n_altdef: "n = Max (insert 0 I')"
      by (simp add: n_def I'_def)
    have "(\<Sum>i\<in>I. fib i) = (\<Sum>i\<in>I'. fib i)"
      by (rule sum.mono_neutral_right) (auto simp: I'_def)
    also have "I' \<in> {{}, {1}}"
      using I by (auto simp: atMost_Suc I'_def)
    hence "(\<Sum>i\<in>I'. fib i) < fib (Suc n) + (if even n then 0 else 1)"
      by (auto simp: n_altdef)
    finally show ?thesis
      by (simp add: n_def)
  next
    case I: False
    hence "I \<noteq> {}"
      by auto
    have "n \<in> I"
      using \<open>I \<noteq> {}\<close> by (auto simp: n_def)
    have "I \<subseteq> {..n}"
      by (auto simp: n_def)
    then have "n \<ge> 2"
      using I by force

    define I' where "I' = I - {n}"
    define n' where "n' = Max (insert 0 I')"
    have "n' \<le> n - 2"
    proof -
      have "insert 0 I' \<subseteq> insert 0 (I - {n, n-1})"
        using psubset.prems[of "n - 1"] \<open>n \<in> I\<close> \<open>n \<ge> 2\<close> by (auto simp: I'_def)
      also have "\<dots> \<subseteq> {..n-2}"
        using \<open>I \<subseteq> {..n}\<close> by auto
      finally show "n' \<le> n - 2"
        unfolding n'_def by (subst Max_le_iff) (auto simp: I'_def)
    qed

    have I_eq: "I = insert n I'" and [simp]: "n \<notin> I'" "finite I'"
      using \<open>n \<in> I\<close> by (auto simp: I'_def)
    have "(\<Sum>i\<in>I. fib i) = (\<Sum>i\<in>I'. fib i) + fib n"
      using \<open>n \<in> I\<close> by (simp add: I_eq)
    also have "(\<Sum>i\<in>I'. fib i) < fib (Suc n') + (if even n' then 0 else 1)"
      unfolding n'_def
    proof (rule psubset.IH)
      show "I' \<subset> I"
        using \<open>n \<in> I\<close> by (auto simp: I'_def)
    next
      show "Suc i \<notin> I'" if "i \<in> I'" for i
        using that psubset.prems by (auto simp: I'_def)
    qed
    also have "fib (Suc n') + (if even n' then 0 else 1) \<le> fib (n - 1) + (if even n then 0 else 1)"
    proof (cases "n = n' + 2 \<or> even n'")
      case True
      thus ?thesis using \<open>n' \<le> n - 2\<close> \<open>n \<ge> 2\<close> by (auto intro!: fib_mono simp: le_Suc_eq)
    next
      case False
      with \<open>n \<ge> 2\<close> and \<open>n' \<le> n - 2\<close> have "n \<ge> n' + 3" "n \<ge> 4"
        by presburger+
      hence "fib (Suc n') < fib (n - 1)"
        using \<open>n' \<le> n - 2\<close> \<open>n \<ge> 2\<close> by (intro fib_strict_mono) auto
      thus ?thesis
        by auto
    qed
    also have "fib (n - 1) + (if even n then 0 else 1) + fib n =
               fib (Suc n) + (if even n then 0 else 1)"
      using \<open>n \<ge> 2\<close> by (subst (3) fib_rec) auto
    finally show ?thesis
      by (simp add: n_def)
  qed
qed

(*
  Manuel: This form is a bit nicer to use because you don't have to use exactly the maximum but
    any upper bound is fine. One could probably also prove this one directly by induction instead
    of using the maximum, but it probably wouldn't improve things that much.
*)
lemma sum_nonconsec_fib_less_strong:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I" "I \<subseteq> {..n}"
  shows   "(\<Sum>i\<in>I. fib i) < fib (Suc n) + (if even n then 0 else 1)"
proof -
  define m where "m = Max (insert 0 I)"
  have "m \<le> n"
    unfolding m_def using assms by (subst Max_le_iff) auto
  have "(\<Sum>i\<in>I. fib i) < fib (Suc m) + (if even m then 0 else 1)"
    unfolding m_def by (rule sum_nonconsec_fib_less_strong_aux) (use assms in auto)
  also have "\<dots> \<le> fib (Suc n) + (if even n then 0 else 1)"
  proof (cases "odd m \<and> even n \<and> m > 0")
    case False
    have "fib (Suc m) \<le> fib (Suc n)"
      by (rule fib_mono) (use \<open>m \<le> n\<close> in auto)
    thus ?thesis using False by auto
  next
    case True
    hence "m \<noteq> n"
      by auto
    with \<open>m \<le> n\<close> have "m < n" by simp
    hence "fib (Suc m) < fib (Suc n)"
      using True by (intro fib_strict_mono) auto
    thus ?thesis
      by auto
  qed
  finally show ?thesis .
qed

lemma sum_nonconsec_fib_less_even:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I" "I \<subseteq> {..n}" "even n"
  shows   "(\<Sum>i\<in>I. fib i) < fib (Suc n)"
  using sum_nonconsec_fib_less_strong[of I n] assms by auto

lemma sum_nonconsec_fib_le:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I" "I \<subseteq> {..n}"
  shows   "(\<Sum>i\<in>I. fib i) \<le> fib (Suc n)"
proof -
  have "(\<Sum>i\<in>I. fib i) < fib (Suc n) + (if even n then 0 else 1)"
    by (intro sum_nonconsec_fib_less_strong) (use assms in auto)
  also have "\<dots> \<le> fib (Suc n) + 1"
    by auto
  finally show ?thesis
    by linarith
qed



(* 
  Manuel: Unfortunately, the above is not quite suitable because your sums below do not contain
    the index i = 1, which is important, because in that case we can actually drop the annoying
    case distinction between even and odd:
*)
lemma sum_nonconsec_fib_less_strong_aux':
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I" "1 \<notin> I"
  shows   "(\<Sum>i\<in>I. fib i) < fib (Suc (Max (insert 0 I)))"
  using assms
proof (induction I rule: finite_psubset_induct)
  case (psubset I)
  define n where "n = Max (insert 0 I)"
  have [simp]: "finite I"
    by fact
  show ?case
  proof (cases "I \<subseteq> {0}")
    case I: True
    have "(\<Sum>i\<in>I. fib i) = (\<Sum>i\<in>{}. fib i)"
      by (rule sum.mono_neutral_right) (use psubset.prems I in auto)
    thus ?thesis
      by (simp add: fib_pos_iff)
  next
    case I: False
    hence "I \<noteq> {}"
      by auto
    have "n \<in> I"
      using \<open>I \<noteq> {}\<close> by (auto simp: n_def)
    have "I \<subseteq> {..n}"
      by (auto simp: n_def)
    then have "n \<ge> 2"
    proof -
      from I obtain k where k: "k \<in> I" "k \<noteq> 0"
        by auto
      with psubset.prems have "k \<noteq> 1"
        by auto
      with k have "k \<ge> 2"
        by linarith
      with k show ?thesis
        unfolding n_def by (subst Max_ge_iff) auto
    qed

    define I' where "I' = I - {n}"
    define n' where "n' = Max (insert 0 I')"
    have "n' \<le> n - 2"
    proof -
      have "insert 0 I' \<subseteq> insert 0 (I - {n, n-1})"
        using psubset.prems(1)[of "n - 1"] \<open>n \<in> I\<close> \<open>n \<ge> 2\<close> by (auto simp: I'_def)
      also have "\<dots> \<subseteq> {..n-2}"
        using \<open>I \<subseteq> {..n}\<close> by auto
      finally show "n' \<le> n - 2"
        unfolding n'_def by (subst Max_le_iff) (auto simp: I'_def)
    qed

    have I_eq: "I = insert n I'" and [simp]: "n \<notin> I'" "finite I'"
      using \<open>n \<in> I\<close> by (auto simp: I'_def)
    have "(\<Sum>i\<in>I. fib i) = (\<Sum>i\<in>I'. fib i) + fib n"
      using \<open>n \<in> I\<close> by (simp add: I_eq)
    also have "(\<Sum>i\<in>I'. fib i) < fib (Suc n')"
      unfolding n'_def
    proof (rule psubset.IH)
      show "I' \<subset> I"
        using \<open>n \<in> I\<close> by (auto simp: I'_def)
    next
      show "Suc i \<notin> I'" if "i \<in> I'" for i
        using that psubset.prems by (auto simp: I'_def)
    qed (use \<open>1 \<notin> I\<close> in \<open>auto simp: I'_def\<close>)
    also have "fib (Suc n') \<le> fib (n - 1)"
      using \<open>n' \<le> n - 2\<close> \<open>n \<ge> 2\<close> by (intro fib_mono) auto
    also have "fib (n - 1) + fib n = fib (Suc n)"
      using \<open>n \<ge> 2\<close> by (subst (3) fib_rec) auto
    finally show ?thesis by (simp add: n_def)
  qed
qed

lemma sum_nonconsec_fib_less_strong':
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> Suc i \<notin> I" "I \<subseteq> {..n} - {1}"
  shows   "(\<Sum>i\<in>I. fib i) < fib (Suc n)"
proof -
  define m where "m = Max (insert 0 I)"
  have "m \<le> n"
    unfolding m_def using assms by (subst Max_le_iff) auto
  have "(\<Sum>i\<in>I. fib i) < fib (Suc m)"
    unfolding m_def by (rule sum_nonconsec_fib_less_strong_aux') (use assms in auto)
  also have "\<dots> \<le> fib (Suc n)"
    using \<open>m \<le> n\<close> by (intro fib_mono) auto
  finally show ?thesis .
qed


lemma Zeckendorf_theorem: 
  fixes n :: nat
  shows "\<exists>!I. finite I \<and> (\<forall> a b. (a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b+1)) \<and> n = (\<Sum>(i::nat)\<in>I. fib (i+2))"
proof - 
  (* Manuel: defining this as a predicate causes less boilerplate when writing the proof.
       Also, it makes sense to write the non-consecutivity in this more compact form. *)
  define P where "P = (\<lambda>I. finite I \<and> (\<forall>i\<in>I. Suc i \<notin> I) \<and> n = (\<Sum>i\<in>I. fib (i+2)))"

  (* Manuel: breaking it up into smaller facts like this reduces copy-pasting proofs for the
       very similar symmetric cases. *)
  have 1: "I = J" if I: "P I" and J: "P J" and "I \<subseteq> J" for I J
  proof (rule ccontr)
    assume "I \<noteq> J"
    with \<open>I \<subseteq> J\<close> obtain j where "j \<in> J - I"
      by blast
    hence "(\<Sum>i\<in>I. fib (i + 2)) < (\<Sum>i\<in>J. fib (i + 2))"
      using J \<open>I \<subseteq> J\<close> by (intro sum_strict_mono2[of _ _ j]) (auto simp: P_def fib_pos_iff)
    with I J show False
      by (simp add: P_def)
  qed

  have 2: False if I: "P I" and J: "P J"
    and symmetry_break: "\<not>I \<subseteq> J" "\<not>J \<subseteq> I" "Max (I - J) \<le> Max (J - I)" for I J
  proof -
    define \<I> where \<I>_def: "\<I> = I - J"
    define \<J> where \<J>_def: "\<J> = J - I"
    have none_in_common: "\<I> \<inter> \<J> = {}" and "\<I> \<noteq> {}" and "\<J> \<noteq> {}"
      unfolding \<I>_def \<J>_def using symmetry_break by auto

    (* Manuel: use "define" instead of "Obtain" if you want to make local definitions *)
    define \<II> where "\<II> = Max \<I>"
    (* Manuel: you just have to show that the set in question is finite and non-empty. *)
    have "finite \<I>"
      unfolding \<I>_def using I by (auto simp: P_def)
    have "\<II> \<in> \<I>"
      unfolding \<II>_def using \<open>\<I> \<noteq> {}\<close> \<open>finite \<I>\<close> by (intro Max_in) auto
    have \<II>_ge: "i \<le> \<II>" if "i \<in> \<I>" for i
      using that \<open>finite \<I>\<close> by (auto simp: \<II>_def)

    obtain \<JJ> where \<JJ>_def: "\<JJ> = Max \<J>"     (*I'm confused by we are using "obtain" here whereas above we are using "define".
                                 Also confused why the nonempty and finite clauses are coming after we obtain the element!*)
      by blast
    have "finite \<J>"
      unfolding \<J>_def using J by (auto simp: P_def)
    have "\<JJ> \<in> \<J>"
      unfolding \<JJ>_def using \<open>\<J> \<noteq> {}\<close> \<open>finite \<J>\<close> by (intro Max_in) auto
    have \<JJ>_ge: "j \<le> \<JJ>" if "j \<in> \<J>" for j
      using that \<open>finite \<J>\<close> by (auto simp: \<JJ>_def)

    have "\<II> \<le> \<JJ>"
      using symmetry_break by (simp add: \<II>_def \<JJ>_def \<I>_def \<J>_def)
    moreover have "\<II> \<noteq> \<JJ>"
      using none_in_common \<open>\<II> \<in> \<I>\<close> \<open>\<JJ> \<in> \<J>\<close> by blast
    ultimately have "\<II> < \<JJ>"
      by linarith

    have "(\<Sum>i\<in>\<I>. fib (i + 2)) = (\<Sum>i\<in>(\<lambda>i. i+2) ` \<I>. fib i)"
      by (subst sum.reindex) (auto simp: inj_on_def)
    also have "\<dots> < fib (Suc (\<II> + 2))"
    proof (intro sum_nonconsec_fib_less_strong')
      fix i assume "i \<in> (\<lambda>i. i + 2) ` \<I>"
      thus "Suc i \<notin> (\<lambda>i. i + 2) ` \<I>"
        using I by (auto simp: \<I>_def P_def)
    qed (use \<open>finite \<I>\<close> \<II>_ge in auto)
    also have "\<dots> \<le> fib (\<JJ> + 2)"
      by (intro fib_mono) (use \<open>\<II> < \<JJ>\<close> in auto)
    also have "fib (\<JJ> + 2) \<le> (\<Sum>i\<in>\<J>. fib (i + 2))"
      by (intro member_le_sum) (use \<open>finite \<J>\<close> \<open>\<JJ> \<in> \<J>\<close> in auto)
    also have "(\<Sum>i\<in>\<J>. fib (i + 2)) = (\<Sum>i\<in>\<I>. fib (i + 2))"
    proof -
      have "(\<Sum>i\<in>\<J>. fib (i + 2)) + (\<Sum>i\<in>I\<inter>J. fib (i + 2)) = (\<Sum>i\<in>\<J>\<union>(I\<inter>J). fib (i + 2))"
        using I J by (intro sum.union_disjoint [symmetric]) (auto simp: P_def \<J>_def)
      also have "\<J>\<union>(I\<inter>J) = J"
        by (auto simp: \<J>_def)
      also have "(\<Sum>i\<in>J. fib (i + 2)) = n"
        using J by (simp add: P_def)
      finally have A: "(\<Sum>i\<in>\<J>. fib (i + 2)) + (\<Sum>i\<in>I\<inter>J. fib (i + 2)) = n" .

      have "(\<Sum>i\<in>\<I>. fib (i + 2)) + (\<Sum>i\<in>I\<inter>J. fib (i + 2)) = (\<Sum>i\<in>\<I>\<union>(I\<inter>J). fib (i + 2))"
        using I J by (intro sum.union_disjoint [symmetric]) (auto simp: P_def \<I>_def)
      also have "\<I>\<union>(I\<inter>J) = I"
        by (auto simp: \<I>_def)
      also have "(\<Sum>i\<in>I. fib (i + 2)) = n"
        using I by (simp add: P_def)
      finally have "(\<Sum>i\<in>\<I>. fib (i + 2)) + (\<Sum>i\<in>I\<inter>J. fib (i + 2)) = n" .
      with A show ?thesis
        by simp
    qed
    finally show False
      by linarith
  qed

  have "I = J" if "P I" "P J" for I J
    using 1[of I J] and 1[of J I] and 2[of I J] and 2[of J I] and that
    by fastforce
  moreover have "\<exists>I. P I"
    using Zeckendorf_theorem_existence[of n] unfolding P_def by auto
  ultimately have "\<exists>!I. P I"
    by blast
  also have "P = (\<lambda>I. finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>i\<in>I. fib (i + 2)))"
    unfolding P_def by auto
  finally show ?thesis .
qed





value "fact(3 )"



lemma finite_fib_le: "finite {i. fib i \<le> n}"
  sorry


(*
proof - 
  have "{i. fib i \<le> n } \<subseteq> {m. m \<le> n}"
    sorry
  then show ?thesis
    by (metis finite_Collect_le_nat finite_subset)
*)

(*
proof(induction n)
  show "finite {i. fib i \<le> 0}"
    by (metis Fib.fib1 One_nat_def Suc_le_eq fib_mono finite_nat_set_iff_bounded_le le_zero_eq less_not_refl linear mem_Collect_eq)
next
  fix n
  assume "finite {i. fib i \<le> n}"
  have "{i. fib i \<le> Suc n} = {i. fib i \<le> n} \<union> {i. fib i = Suc n}"
    by auto
  show "finite {i. fib i \<le> Suc n}"
  proof(cases "\<exists> i. fib i = Suc n")
    assume "\<exists>i. fib i = Suc n"
    then obtain i where i_def: "fib i = Suc n"
      by blast
    have "\<exists>!i. fib i = Suc n"
    proof(cases "n \<le> 2")
      assume "n \<le> 2"
      then consider "n = 0" | "n = 1" | "n = 2" 
        by linarith
      show  "\<exists>!i. fib i = Suc n"
        oops

      then obtain j where j_def: "fib j = Suc n \<and> i \<noteq> j"
        by (metis i_def)
      then have "Suc n < Suc n"
        using fib_less_iff
*)    





definition fib_step :: "nat \<Rightarrow> nat" where
   "fib_step n = Max {i::nat. fib i \<le> n}"

lemma fib_step_pos: "n > 0 \<Longrightarrow> fib_step n > 0"
   sorry

function fib_encode :: "nat \<Rightarrow> nat set" where
   "fib_encode n =
      (if n = 0 then {} else insert (fib_step n - 2) (fib_encode (n -
fib_step n)))"
   by auto
termination
   by (relation "measure id") (use fib_step_pos in auto)


 value "fib_encode(3::nat)"









end          
      












