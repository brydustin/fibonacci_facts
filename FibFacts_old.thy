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








(*begin on page 21*)

lemma Exercise6a: "(\<Sum>k \<in> {..n}. fib k) = fib (n+2) - 1"     (*Also exercise 7 of Andrews*)
proof(induction n)
  show "sum fib {..0} = fib (0 + 2) - 1"
    by simp
next 
  fix n 
  assume "sum fib {..n} = fib (n + 2) - 1"
  then show "sum fib {..Suc n} = fib (Suc n + 2) - 1"
    by force
qed



lemma Exercise8_Andrews: "(\<Sum>k \<in> {1..n}. fib (2*k-1)) = fib (2*n)"
  by(induct n rule: fib.induct, simp_all)


lemma Exercise9_Andrews: "(\<Sum>k \<in> {..n}. fib (2*k)) = fib (2*n+1) - 1"
  by(induct n rule: fib.induct, simp_all, simp add: numeral_3_eq_3)




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
  also have "... = fib (2 * n + 1) + fib (2*n +2) -1 "
    by(induct n rule: fib.induct, simp_all, simp add: numeral_3_eq_3)
  also have "... = fib (2 * n + 3)  -1 "
    by (simp add: add.commute numeral_3_eq_3)
  also have "... = fib (2 * Suc n + 1) - 1"
    by (simp add: numeral_3_eq_3)
  then show "(\<Sum>k\<le>Suc n. fib (2 * k)) = fib (2 * Suc n + 1) - 1"
    using calculation by auto
qed

  

lemma Exercise6c: "(\<Sum>k \<in> {1..n}. fib (2*k-1)) = fib (2*n)"
  by (induct n rule: fib.induct, simp+)





lemma Exercise6d: "(\<Sum>k \<in> {..n}. fib(k)*fib(k)) = fib(n)*fib(n+1)"
  by (metis Suc_eq_plus1 fib_mult_eq_sum_nat mult.commute)
(*Already solved as "fib_mult_eq_sum_nat" but I prefer this representation and this order of presentation.*)







(*
lemma Exercise6e: "fib(n)*fib(n+2) = (fib(n+1)*fib(n+1))+(-1)^(n+1)"   *)  (*This is how it is stated in Lanski*)
lemma Exercise6e: "int(fib((n+1)-1)*fib((n+1)+1)) -  int(fib(n+1)*fib(n+1)) = (-1::int)^(n+1)"   (*Also Exercise 10 in Andrews*)   (*Also known as Cassini's Identity*)
  by(induct n rule: fib.induct, auto, smt (verit, best) left_diff_distrib right_diff_distrib)
  








lemma Exercise11_Andrews: "(\<Sum>k \<in> {2..(2*n)}. fib(k-1)*fib(k)) = fib(2*n)*fib(2*n)"
  by(induct n rule: fib.induct, simp+, simp add: comm_semiring_class.distrib distrib_left)


lemma Exercise12_Andrews: "(\<Sum>k \<in> {2..(2*n+1)}. fib(k-1)*fib(k)) = fib(2*n+1)*fib(2*n+1)-1"
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


(*Consider proving exercise 13 of 3.1 from Andrews*)
(* https://proofwiki.org/wiki/Fibonacci_Number_as_Sum_of_Binomial_Coefficients *)




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
    assume "\<not> n \<le> 2" then have "2 < n"
      by (meson not_le)

    have index_change: "(\<Sum>k = 2..n. ((n+1) choose k) * fib (m + k)) = (\<Sum>k = 1..(n-1). ((n+1) choose (k+1)) * fib (m + (k+1)))"
      sorry      


    have another_index_change: "(\<Sum>k = 0..(n-2). ((n choose (k+1)) * fib (m + (k+1)))) = (\<Sum>k = 1..(n-1). ((n choose k) * fib (m + k)))"
      sorry



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
  proof(cases "n \<le> 2",simp)
    assume "n \<le> 2" 
    show "(\<Sum>k = Suc 0..n. (Suc n choose k) * fib k) + fib (Suc n) = fib (Suc (2 * n)) + fib (2 * n)"
    proof(cases "n = 0", simp)
      assume "n \<noteq> 0"
      show ?thesis
      proof(cases "n=1",simp)
        show "Suc (Suc 0) = fib 3"
          by (simp add: numeral_3_eq_3)
      next
        assume "n \<noteq> 1" then have "n = 2"
          by (metis One_nat_def \<open>n \<le> 2\<close> \<open>n \<noteq> 0\<close> less_2_cases_iff nat_less_le)
        have "(\<Sum>k = 1..Suc 2. (Suc 2 choose k) * fib k) = ((3 choose 1) * fib 1) + ((3 choose 2) * fib 2) + ((3 choose 3)* fib(3))"
          by (smt (z3) Suc_1 Suc_eq_plus1 add_diff_cancel_left' binomial_1 binomial_Suc_n binomial_eq_0_iff binomial_n_n le_add1 nat.simps(3) numeral_3_eq_3 sum.atLeast_Suc_atMost sum.cl_ivl_Suc sum.ub_add_nat)
        also have "... = (3*1 + 3*1 + 1*2)"
          by (metis Suc_1 binomial_1 binomial_Suc_n binomial_n_n fib_1 fib_2 fib_plus_2 numeral_3_eq_3 plus_1_eq_Suc)
        also have "... = fib (Suc (2 * n)) + fib (2 * n)"
          by (simp add: \<open>n = 2\<close> mult_2_right numeral_3_eq_3)
        then show ?thesis
          by (simp add: \<open>n = 2\<close> numeral_3_eq_3 sum.atLeast_Suc_atMost)
      qed
    qed
  next
    assume "\<not> n \<le> 2" then have "2 < n"
      by auto
    have index_shift: "(\<Sum>k = 1..n. ((n choose (k-1))* fib k  )) = (\<Sum>k = 0..(n-1). ((n choose k)* fib (k+1)  ))"
      sorry
      
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

  

lemma Zeckendorf_theorem: 
  fixes n :: nat
  shows "\<exists>!I. finite I \<and> (\<forall> a b. (a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b+1)) \<and> n = (\<Sum>(i::nat)\<in>I. fib (i+2))"
proof - 
  have "\<exists>I. finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>(i::nat)\<in>I. fib (i + 2))"
    using Zeckendorf_theorem_existence by presburger
  then obtain I where I_def: "finite I \<and> (\<forall>a b. a \<in> I \<and> b \<in> I \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>(i::nat)\<in>I. fib (i + 2))"
    by presburger
  have "\<And> J. finite J \<and> (\<forall>a b. a \<in> J \<and> b \<in> J \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>(i::nat)\<in>J. fib (i + 2)) \<Longrightarrow> J = I"
  proof - 
    fix J
    assume a1: "finite J \<and> (\<forall>a b. a \<in> J \<and> b \<in> J \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>(i::nat) \<in>J. fib (i + 2))"
    obtain \<I> where \<I>_def: "\<I> = I - (I\<inter>J)"
      by blast
    obtain \<J> where \<J>_def: "\<J> = J - (I\<inter>J)"
      by blast
    show "J =  I"
    proof(cases "\<I> = {}")
      assume  "\<I> = {}" 
      then have "I \<subseteq> J"
        by (simp add: \<I>_def)
      show "J= I"
      proof(rule ccontr)
        assume BWOC: "J \<noteq> I"
        then have "\<exists>j. (j::nat) \<in> J \<and> j \<notin> I"
          using \<open>I \<subseteq> J\<close> by blast
        then obtain j::nat where j_def: "j \<in> J \<and> j \<notin> I"
          by blast
        then have "I \<union> {j} \<subseteq> J"
          by (simp add: \<open>I \<subseteq> J\<close>)
        have "n = (\<Sum>i\<in>I. fib (i + 2))"
          using I_def by presburger
        also have "... < (\<Sum>i\<in>I. fib (i + 2)) + 1"
          by linarith
        also have "... \<le> (\<Sum>i\<in>I. fib (i + 2)) + (\<Sum>i\<in>{j}. fib (i + 2))"
          by (simp add: Suc_leI fib_neq_0_nat)
        also have "... = (\<Sum>i\<in>I\<union>{j}. fib (i + 2))"
          by (simp add: I_def j_def)
        also have "... \<le> (\<Sum>i\<in>J. fib (i + 2))"
          by (meson \<open>I \<union> {j} \<subseteq> J\<close> a1 sum_mono2 zero_le)
        also have "... = n"
          using a1 by blast
        then have "n < n"
          using calculation by auto
        then show False
          by simp
      qed
    next
      assume "\<I> \<noteq> {}"
      obtain i where i_def: "(i::nat) \<in> \<I>"
        using \<open>\<I> \<noteq> {}\<close> by blast        
      show ?thesis
      proof(cases "\<J> = {}")
        assume  "\<J> = {}" 
        then have "J \<subseteq> I"
          by (simp add: \<J>_def)
        show "J= I"
        proof(rule ccontr)
          assume BWOC: "J \<noteq> I"
        then have "\<exists>i. (i::nat) \<in> I \<and> i \<notin> J"
          using \<open>J \<subseteq> I\<close> by blast
        then obtain i::nat where i_def: "i \<in> I \<and> i \<notin> J"
          by blast
        then have "J \<union> {i} \<subseteq> I"
          by (simp add: \<open>J \<subseteq> I\<close>)
        have "n = (\<Sum>j\<in>J. fib (j + 2))"
          using a1 by blast
        also have "... < (\<Sum>j\<in>J. fib (j + 2)) + 1"
          by linarith
        also have "... \<le> (\<Sum>j\<in>J. fib (j + 2)) + (\<Sum>j\<in>{i}. fib (j + 2))"
          by (simp add: Suc_leI fib_neq_0_nat)
        also have "... = (\<Sum>j\<in>J\<union>{i}. fib (j + 2))"
          by (simp add: a1 i_def)
        also have "... \<le> (\<Sum>i\<in>I. fib (i + 2))"
          by (meson I_def \<open>J \<union> {i} \<subseteq> I\<close> sum_mono2 zero_le)
        also have "... = n"
          using I_def by blast
        then have "n < n"
          using calculation by auto
        then show False
          by simp
      qed
     next
      assume "\<J> \<noteq> {}"

      have equals_removed_equal: " (\<Sum>i\<in>\<I>. fib (i + 2)) = (\<Sum>i\<in>\<J>. fib (i + 2))"
        by (smt (z3) I_def \<I>_def \<J>_def a1 add_diff_cancel_left' inf_commute inf_sup_aci(4) sum.Int_Diff)
  
      have none_in_common: "\<I> \<inter> \<J> = {}"
        using \<I>_def \<J>_def by fastforce
      
  
      obtain \<II> where \<II>_def: "\<II>  = Max \<I>"
        by blast
     
      then have "\<II> \<in> \<I>"   (*This is precisely why we needed this set to be nonempty.... but do we ever actually use this?  Possibly for 684 and 709*)
        sorry
      
  
  
  
      obtain \<JJ> where \<JJ>_def: "\<JJ> = Max \<J>"
        by blast

      then have "\<JJ> \<in>  \<J>"
        sorry
    
    
      have Maxs_unequal: "\<II> \<noteq> \<JJ>"
        by (metis \<open>\<II> \<in> \<I>\<close> \<open>\<JJ> \<in> \<J>\<close> disjoint_iff_not_equal none_in_common)

      show ?thesis
      proof(cases "\<II> < \<JJ>")
        assume "\<II> < \<JJ>"
        have "(\<Sum>i\<in>\<I>. fib (i + 2)) < fib((\<II>+1) + 2)"
          sorry
        then have "fib(\<II> + 2) < fib((\<II>+1) + 2)"
          by (metis Suc_eq_plus1 add_2_eq_Suc' add_diff_cancel_left' add_gr_0 fib_neq_0_nat fib_plus_2 zero_less_diff zero_less_one)
        have "fib((\<II>+1) + 2) \<le> fib(\<JJ> + 2)"
          by (metis \<open>\<II> < \<JJ>\<close> add.commute discrete fib_mono nat_add_left_cancel_le)
        then have "(\<Sum>i\<in>\<I>. fib (i + 2)) < fib(\<JJ> + 2)"
          using \<open>(\<Sum>i\<in>\<I>. fib (i + 2)) < fib (\<II> + 1 + 2)\<close> by linarith

        have "(\<Sum>i\<in>\<J>. fib (i + 2)) \<ge> fib(\<JJ> + 2)"
        proof - 
          have "(\<Sum>i\<in>\<J>. fib (i + 2)) = (\<Sum>i\<in>(\<J>-{\<JJ>}). fib (i + 2)) + (\<Sum>i\<in>({\<JJ>}). fib (i + 2))"
            by (metis (mono_tags, lifting) \<J>_def \<open>\<JJ> \<in> \<J>\<close> a1 add.left_commute add.right_neutral empty_iff finite.emptyI finite_Diff insert_Diff insert_Diff_single sum.empty sum.insert sum.insert_remove)
          also have "... \<ge> (\<Sum>i\<in>({\<JJ>}). fib (i + 2))"
            by presburger
          then show ?thesis 
            using calculation by auto
        qed        
        then have False
          using \<open>(\<Sum>i\<in>\<I>. fib (i + 2)) < fib (\<JJ> + 2)\<close>  equals_removed_equal by linarith
        then show ?thesis 
          by simp
      next
        assume " \<not> \<II> < \<JJ>" then have "\<JJ> < \<II>"
          by (meson Maxs_unequal nat_neq_iff)
        have "(\<Sum>i\<in>\<J>. fib (i + 2)) < fib((\<JJ>+1) + 2)"
          sorry
        then have "fib(\<JJ> + 2) < fib((\<JJ>+1) + 2)"
          by (metis One_nat_def Suc_eq_plus1 add_Suc_right fib_neq_0_nat fib_plus_2 less_add_same_cancel1 numeral_2_eq_2 trans_less_add2 zero_less_one)

        have "fib((\<JJ>+1) + 2) \<le> fib(\<II> + 2)"
          by (metis \<open>\<JJ> < \<II>\<close> add.commute discrete fib_mono nat_add_left_cancel_le)

        then have "(\<Sum>i\<in>\<J>. fib (i + 2)) < fib(\<II> + 2)"
          using \<open>(\<Sum>i\<in>\<J>. fib (i + 2)) < fib (\<JJ> + 1 + 2)\<close> by linarith


        have "(\<Sum>i\<in>\<I>. fib (i + 2)) \<ge> fib(\<II> + 2)"
        proof - 
          have "(\<Sum>i\<in>\<I>. fib (i + 2)) = (\<Sum>i\<in>(\<I>-{\<II>}). fib (i + 2)) + (\<Sum>i\<in>({\<II>}). fib (i + 2))"
            by (metis (no_types, lifting) I_def \<I>_def \<open>\<II> \<in> \<I>\<close> empty_iff finite.emptyI finite_Diff group_cancel.add2 nat_arith.rule0 sum.empty sum.insert_if sum.insert_remove)
          also have "... \<ge> (\<Sum>i\<in>({\<II>}). fib (i + 2))"
            by presburger
          then show ?thesis
            using calculation by force
        qed
        then have False
          using \<open>(\<Sum>i\<in>\<J>. fib (i + 2)) < fib (\<II> + 2)\<close> equals_removed_equal by linarith
        then show ?thesis
          by simp
      qed
    qed
  qed
qed
  show ?thesis
    by (metis I_def \<open>\<And>J. finite J \<and> (\<forall>a b. a \<in> J \<and> b \<in> J \<longrightarrow> a \<noteq> b + 1) \<and> n = (\<Sum>i\<in>J. fib (i + 2)) \<Longrightarrow> J = I\<close>)
qed

end          
      




(*
(*Main lemma*)   Old version.... leave alone for now

lemma exercise10: 
  fixes n :: nat
  shows "\<exists>I. finite I \<and> n = (\<Sum>i\<in>I. fib (i+2))"
proof(induction n rule: less_induct)
  fix x 
  assume  induction_hypothesis: "(\<And>y. y < x \<Longrightarrow> \<exists>I. finite I \<and> y = (\<Sum>i\<in>I. fib (i+2)))"
  show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
  proof(cases "x \<le> 2") 
    show "x \<le> 2 \<Longrightarrow> \<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i+2))"
    proof(cases "x < 2")
      assume "x < 2" then show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i+2))"
        by (smt (verit, del_insts) One_nat_def add.left_neutral empty_iff fib_2 finite.intros(1) less_2_cases_iff nat_arith.rule0 sum.empty sum.infinite sum.insert)
    next 
      show "x \<le> 2 \<Longrightarrow> \<not> x < 2 \<Longrightarrow> \<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i+2))"
        by (smt (z3) Suc_1 empty_iff fib_1 fib_2 fib_plus_2 finite.intros(1) finite_insert nat_arith.rule0 nat_less_le plus_1_eq_Suc sum.empty sum.insert)
    qed
  next
    assume "\<not> x \<le> 2"
    then have gt_2: "2 < x"
      by (meson not_le)
    then have  "\<exists>I. finite I \<and> x-2 = (\<Sum>i\<in>I. fib (i+2))"   
      using induction_hypothesis by auto
    then obtain I where I_def: "finite I \<and> x-2 = (\<Sum>i\<in>I. fib (i+2))"
      by auto(*
    then have "(\<exists>m. {..m} = I) \<or> \<not>(\<exists>m. {..m} = I)"  (*Either I is a consecutive list of numbers starting at zero or not*)
      by blast*)
    show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i+2))"
    proof(cases "(\<exists>m. {..m} = I)")
      assume "\<exists>m. {..m} = I"
      then obtain m where m_def: "{..m} = I"
        by blast
      obtain J where J_def: "J={m+2}"
        by simp


      have x_plus_1: "x = (1+ (x-2)) + 1"
        using gt_2 by force  
      also have "... =  (fib(1) + (\<Sum>k \<in> {..m}. fib(k+2))) + 1"
        using I_def m_def by force
      also have "... = (fib(0) + fib(1) +  (\<Sum>k \<in> {2..(m+2)}. fib(k))) + 1"
        by(induct m, auto)
      also have "... = (\<Sum>k \<in> {..(m+2)}. fib(k)) + 1"
        by (metis Exercise6a Fib.fib0 add.left_neutral add_2_eq_Suc' diff_Suc_1 fib_2 plus_1_eq_Suc sum.atMost_Suc sum_up_index_split)
      also have "... = fib((m+2)+2)"
        by (simp add: Exercise6a fib_neq_0_nat)
      also have "... = (\<Sum>k \<in> J. fib(k+2))"
        by (simp add: J_def)
      then show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i+2))"
        by (metis J_def calculation finite.emptyI finite.insertI) 
    next
      assume "\<nexists>m. {..m} = I"
      obtain ordered_list where ordered_list_def: "sorted_list_of_set(I) = ordered_list"
        by blast                                                 
      then have nonempty_list: "ordered_list \<noteq> []"
        using I_def gt_2 by auto      
      obtain \<alpha> where \<alpha>_def: "\<alpha> =  Min {j :: nat. (j+2) < ordered_list!j}"  (*This follows presumably by WO ?*)
        by blast
      (*j should be greater than or equal to 2*)

      have ordered_list_is_not_contiguous: "\<nexists>(m::nat). [2..m] = ordered_list"
      proof(rule ccontr, auto)
        show "\<And>x. [2..int x] = map int ordered_list \<Longrightarrow> False"
        proof - 
          fix x 
          assume "[2..int x] = map int ordered_list"
          oops
        
        have fin_set: "finite {j :: nat. j < ordered_list!j}"
        sorry
        
        (*using nonempty_list apply(induct ordered_list, auto)*)



      then have \<alpha>_in_I: "\<alpha> \<in> {j :: nat. j < ordered_list!j}"
        unfolding \<alpha>_def apply(rule linorder_class.Min_in, auto)
      show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
      proof(cases "\<alpha> = 0")  
        assume alpha_zero: "\<alpha> = 0"
        
        have zero_lt_list: "0 < ordered_list!0"  (*2<u_2 *)
               


(* proof(rule ccontr,simp)                (*We may not need to open a proof block... does it help?*)
          assume "ordered_list ! 0 = 0"
          then have "\<alpha> \<noteq> 0"
            sorry
          then show False
            by (simp add: alpha_zero)
        qed*)
        have fact: "x-1 = fib(2) + (\<Sum>i\<in>I. fib (i + 2))"
          using I_def fib_2 ge_2 by linarith
        show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
        proof(cases "1 < ordered_list!0")
          assume " 1 < ordered_list ! 0"
          then have one_not_in_I: "1 \<notin> I"
            sorry
          have "x = fib(1) + fib(2) + (\<Sum>i\<in>I. fib (i + 2))"
            using I_def fib_1 fib_2 ge_2 by linarith
          then have "x = fib(3) + (\<Sum>i\<in>I. fib (i + 2))"
            by (simp add: numeral_Bit1)
          then have "x = (\<Sum>i\<in>{1::nat}. fib (i + 2)) + (\<Sum>i\<in>I. fib (i + 2))"
            by (simp add: numeral_3_eq_3)
          then have "x = (\<Sum>i\<in>({1::nat}\<union> I). fib (i + 2))"
            using I_def one_not_in_I by auto
          then show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i + 2))"
            by (metis I_def finite.emptyI finite.insertI finite_UnI)
        next
          assume "\<not> 1 < ordered_list ! 0"
          then have "1 = ordered_list!0"
            using zero_lt_list by linarith
          then have "x-2 = fib(3) + (\<Sum>i\<in>(I-{1}). fib (i + 2))"  
            sorry    (*The idea here is that we are poping the 3 term out and subtracting it from the set I*)
          then have "x-1 = fib(2) + fib(3) + (\<Sum>i\<in>(I-{1}). fib (i + 2))"    (*N = x-1*)
            by (metis I_def add.assoc fact) 
          show "\<exists>I. finite I \<and> x = (\<Sum>i\<in>I. fib (i + 2))"   (*Recall: x-2 = (\<Sum>i\<in>I. fib (i + 2))" *)
          proof(cases "sorted_list_of_set(I-{1}) = [4::nat..Max(I-{1})]") (*In other words, x-1 = F_2 + F_3 + F_4 +... + F_max*)
                (*Is that really how I want to "case" this?  It's forcing the elements to be integers rather than natural numbers*)


            oops

*)









