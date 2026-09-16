import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.IntervalCases
import Mathlib.NumberTheory.Real.Irrational

-- Exercises

-- 3.2.4.1 Find a natural number n for which n²+n+41 is not prime.
example: ∃ n: Nat, ¬Nat.Prime (n^2 + n + 41) := by
    -- ⊢ ∃ n, ¬Nat.Prime (n ^ 2 + n + 41)
    use 40
    -- ⊢ ¬Nat.Prime (40 ^ 2 + 40 + 41)
    simp
    -- ⊢ ¬Nat.Prime 1681
    rw [Nat.prime_def]
    -- ⊢ ¬(2 ≤ 1681 ∧ ∀ (m : ℕ), m ∣ 1681 → m = 1 ∨ m = 1681)
    simp
    -- ⊢ ∃ x, x ∣ 1681 ∧ ¬x = 1 ∧ ¬x = 1681
    use 41
    -- ⊢ 41 ∣ 1681 ∧ ¬41 = 1 ∧ ¬41 = 1681
    simp

-- 3.2.4.2 Show that the propositions p ∨ q and (¬p) → q are logically equivalent.
example (p q : Prop) : (p ∨ q) = (¬p → q) := by
    -- ⊢ (p ∨ q) = (¬p → q)
    rw [imp_iff_not_or]
    -- ⊢ (p ∨ q) = (¬¬p ∨ q)
    rw [not_not]

-- 3.2.4.3 Show that the proposition (p ∨ q) → r is equivalent to (p → r) ∧ (q → r).
example (p q r: Prop): ((p ∨ q) → r) = ((p → r) ∧ (q → r)) := by
    -- rw [or_imp] would be the direct rule, but we'll show it in more steps instead
    repeat rw [imp_iff_not_or]
    -- ⊢ (¬(p ∨ q) ∨ r) = ((¬p ∨ r) ∧ (¬q ∨ r))
    rw [not_or]
    -- ⊢ (¬p ∧ ¬q ∨ r) = ((¬p ∨ r) ∧ (¬q ∨ r))
    rw [and_or_right]

-- 3.2.4.4 Determine whether each of the following statements is true.
-- If it true, prove it. If it is false, give a counterexample.

-- We will only show claims a and b since c and d are easily (dis)proveable.
-- a. Every prime number is odd.
example: ∃n, Nat.Prime n ∧ 2 ∣ n := by
    -- ⊢ ∃ n, Nat.Prime n ∧ 2 ∣ n
    use 2
    -- ⊢ Nat.Prime 2 ∧ 2 ∣ 2
    apply And.intro
    -- 2 goals
    --
    -- case h.left
    -- ⊢ Nat.Prime 2
    --
    -- case h.right
    -- ⊢ 2 ∣ 2
    exact Nat.prime_two
    -- case h.right
    -- ⊢ 2 ∣ 2
    rfl

-- b. Every prime number greater than 2 is odd.
example (n: Nat): Nat.Prime n ∧ 2 < n → ¬ 2 ∣ n := by
    -- n : ℕ
    -- ⊢ Nat.Prime n ∧ 2 < n → ¬2 ∣ n
    intro ⟨prime, greater⟩
    -- n : ℕ
    -- prime : Nat.Prime n
    -- greater : 2 < n
    -- ⊢ ¬2 ∣ n
    rw [Nat.prime_def] at prime
    -- n : ℕ
    -- prime : 2 ≤ n ∧ ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n
    -- greater : 2 < n
    -- ⊢ ¬2 ∣ n
    rcases prime with ⟨ge, prime⟩
    -- n : ℕ
    -- greater : 2 < n
    -- ge : 2 ≤ n
    -- prime : ∀ (m : ℕ), m ∣ n → m = 1 ∨ m = n
    -- ⊢ ¬2 ∣ n
    specialize prime 2
    -- n : ℕ
    -- greater : 2 < n
    -- ge : 2 ≤ n
    -- prime : 2 ∣ n → 2 = 1 ∨ 2 = n
    -- ⊢ ¬2 ∣ n
    by_contra h_even
    -- n : ℕ
    -- greater : 2 < n
    -- ge : 2 ≤ n
    -- prime : 2 ∣ n → 2 = 1 ∨ 2 = n
    -- h_even : 2 ∣ n
    -- ⊢ False
    specialize prime h_even
    -- n : ℕ
    -- greater : 2 < n
    -- ge : 2 ≤ n
    -- prime : 2 = 1 ∨ 2 = n
    -- h_even : 2 ∣ n
    -- ⊢ False
    cases prime with
    -- We look at what would happen if either side of the ∨ where true
    -- The first leasds to an obvious contradiction as 2 ≠ 1
    | inl => contradiction
    -- The second is also abovious with 2 = n and 2 < n, but requires a bit
    -- more explanation to the prover
    | inr h => {
        -- n : ℕ
        -- greater : 2 < n
        -- ge : 2 ≤ n
        -- h_even : 2 ∣ n
        -- h : 2 = n
        -- ⊢ False
        rw [<-h] at greater
        -- n : ℕ
        -- greater : 2 < 2
        -- ge : 2 ≤ n
        -- h_even : 2 ∣ n
        -- h : 2 = n
        -- ⊢ False
        contradiction
    }

-- 3.2.4.5 Suppose that r, s, and t are integers, such that r evenly divides s
-- and s evenly divides t. Prove that r evenly divides t
example (r s t: Int): r ∣ s ∧ s ∣ t → r ∣ t := by
    -- r s t : ℤ
    -- ⊢ s ∣ r ∧ t ∣ s → t ∣ r
    intro ⟨r_div_s, s_div_t⟩
    -- r s t : ℤ
    -- r_div_s : s ∣ r
    -- s_div_t : t ∣ s
    -- ⊢ t ∣ r
    rw [Int.dvd_def] at r_div_s s_div_t ⊢
    -- r s t : ℤ
    -- r_div_s : ∃ c, r = s * c
    -- s_div_t : ∃ c, s = t * c
    -- ⊢ ∃ c, r = t * c
    rcases r_div_s with ⟨m, rq⟩
    rcases s_div_t with ⟨n, rs⟩
    -- r s t m n : ℤ
    -- rq : r = s * m
    -- rs : s = t * n
    -- ⊢ ∃ c, r = t * c
    rw [rq] at rs
    -- r s t m n : ℤ
    -- rq : r = t * n * m
    -- rs : s = t * n
    -- ⊢ ∃ c, r = t * c
    use m * n
    -- r s t m n : ℤ
    -- rq : r = t * n * m
    -- rs : s = t * n
    -- ⊢ r = t * (n * m)
    rw [← Int.mul_assoc]
    exact rs

-- 3.2.4.6 Prove that for all integers n, if n is odd then n² is odd.
example (n: Int): ¬2 ∣ n →  ¬(2 ∣ n ^ 2) := by
    -- n : ℤ
    -- ⊢ ¬2 ∣ n → ¬2 ∣ n ^ 2
    intro odd squared_even
    -- n : ℤ
    -- odd : ¬2 ∣ n
    -- squared_even : 2 ∣ n ^ 2
    -- ⊢ False
    rw [<-even_iff_two_dvd] at odd
    rw [Int.not_even_iff_odd] at odd
    rw [odd_iff_exists_bit1] at odd
    -- n : ℤ
    -- odd : ∃ b, n = 2 * b + 1
    -- squared_even : 2 ∣ n ^ 2
    -- ⊢ False
    rcases odd with ⟨m, odd⟩
    -- n : ℤ
    -- squared_even : 2 ∣ n ^ 2
    -- m : ℤ
    -- odd : n = 2 * m + 1
    -- ⊢ False
    rw [Int.dvd_def] at squared_even
    rcases squared_even with ⟨p, squared_even⟩
    -- n m : ℤ
    -- odd : n = 2 * m + 1
    -- p : ℤ
    -- squared_even : n ^ 2 = 2 * p
    -- ⊢ False
    rw [odd, pow_succ, pow_one, Int.mul_add, mul_one, <-mul_assoc, mul_comm _ 2,
        mul_assoc _ _ m, <-add_assoc, <-left_distrib] at squared_even
    -- n m : ℤ
    -- odd : n = 2 * m + 1
    -- p : ℤ
    -- squared_even : 2 * ((2 * m + 1) * m + m) + 1 = 2 * p
    -- ⊢ False
    have is_even : Even (2 * p) := by
        rw [even_iff_exists_two_mul]
        use p
    -- is_even : Even (2 * p)
    have is_odd : Odd (2 * ((2 * m + 1) * m + m) + 1) := by
        rw [odd_iff_exists_bit1]
        use ((2 * m + 1) * m + m)
    -- is_odd : Odd (2 * ((2 * m + 1) * m + m) + 1)
    rw [squared_even] at is_odd
    -- is_odd : Odd (2 * p)
    rw [<-Int.not_odd_iff_even] at is_even
    -- is_even : ¬Odd (2 * p)
    -- is_odd : Odd (2 * p)
    contradiction

-- 3.2.4.7 Prove that an integer n is divisible by 3 iff n is divisible by 3.
-- (Hint: give an indirect proof of ‘if n² is divisible by 3 then n is divisible
-- by 3.’)

-- We will do as the hint tells us, and first prove if n² is divisible by 3
-- then n is divisible by 3.
lemma e7_1 {n: ℤ}: 3 ∣ n ^ 2 → 3 ∣ n := by
    intro div_squared
    rw [Int.dvd_def] at div_squared ⊢
    rcases div_squared with ⟨m, div_squared⟩

    -- Set up division into cases of n = 3k + 0, 3k + 1, 3k + 2
    have zero_l_three : Int.ofNat 0  < Int.ofNat 3 :=
        Rat.intCast_lt_intCast.mp rfl
    have n_cases := Int.fdiv_mul_add_fmod n 3
    have k_min := Int.fmod_nonneg_of_pos n zero_l_three
    have k_max := Int.fmod_lt_of_pos n zero_l_three
    interval_cases n.fmod 3 <;> clear k_min k_max zero_l_three
    -- Note that in lean we use a slightly different equation, namely
    -- n = n % 3 * 3 + ... (for 0, 1, 2 on the ...)
    -- where we write "n % 3" as "n.fdiv 3"

    -- first case (0)
    rw [Int.add_zero] at n_cases
    use n.fdiv 3
    rw [mul_comm, eq_comm] at n_cases
    exact n_cases

    -- second case (1)
    rw [<-n_cases] at div_squared
    rw [pow_two] at div_squared
    rw [mul_add] at div_squared
    rw [mul_one] at div_squared
    rw [right_distrib] at div_squared
    rw [one_mul] at div_squared
    rw [<-add_assoc] at div_squared
    rw [mul_comm _ 3] at div_squared
    rw [mul_assoc 3] at div_squared
    rw [<-left_distrib 3 _ _] at div_squared
    rw [<-left_distrib 3 _ _] at div_squared
    set k := (n.fdiv 3 * (3 * n.fdiv 3) + n.fdiv 3 + n.fdiv 3)
    rw [eq_comm]at div_squared
    have divide_k_plus_one := Dvd.intro m div_squared
    rw [Int.dvd_self_mul_add] at divide_k_plus_one
    contradiction

    -- third case (2)
    rw [<-n_cases] at div_squared
    rw [pow_two] at div_squared
    rw [mul_add] at div_squared
    rw [right_distrib] at div_squared
    rw [mul_comm _ 3] at div_squared
    rw [mul_assoc 3] at div_squared
    rw [mul_comm 2 _] at div_squared
    rw [mul_assoc 3] at div_squared
    rw [<-left_distrib 3 _ _] at div_squared
    rw [right_distrib] at div_squared
    rw [<-add_assoc] at div_squared
    rw [mul_assoc 3] at div_squared
    rw [<-left_distrib 3 _ _] at div_squared
    set k := (n.fdiv 3 * (3 * n.fdiv 3) + n.fdiv 3 * 2 + n.fdiv 3 * 2)
    norm_num at div_squared
    rw [eq_comm]at div_squared
    have divide_k_plus_one := Dvd.intro m div_squared
    rw [Int.dvd_self_mul_add] at divide_k_plus_one
    contradiction

-- Now the second part
lemma e7_2 {n: ℤ}: 3 ∣ n → 3 ∣ n ^ 2 := by
    intro div_three
    rw [Int.dvd_def] at div_three ⊢
    rcases div_three with ⟨m, div_three⟩
    rw [div_three, pow_two]
    use m * (3 * m)
    rw [mul_assoc]

-- Combining it together
example (n: ℤ): 3 ∣ n ↔ 3 ∣ n ^ 2 := by
    exact ⟨e7_2, e7_1⟩

-- 3.2.4.8 Prove or disprove each of the following statements.
-- Remember that to disprove a statement we always expect a counterexample!

-- The product of two even integers is even.
example (n m : ℤ): Even n ∧ Even m → Even (n * m) := by
    intro ⟨even_n, even_m⟩
    rw [even_iff_two_dvd, Int.dvd_def] at even_n ⊢
    rcases even_n with ⟨k, even_n⟩
    rw [even_n]
    rw [mul_assoc]
    use k * m

-- The product of two integers is even only if both integers are even.
example: ∃n m: ℤ, ¬(Even n ∧ Even m) ∧ Even (n * m) := by
    use 1, 2
    rw [not_and_or]
    rw [Int.not_even_iff_odd, Int.not_even_iff_odd]
    apply And.intro
    apply Or.intro_left
    rw [Int.odd_iff]
    rfl
    rw [Int.even_iff]
    rfl

-- The product of two rational numbers is rational.
example (n m : ℚ): ∃ num den, mkRat num den = n * m := by
    use n.num * m.num, n.den * m.den
    rw [Rat.mkRat_eq_divInt]
    rw [Int.natCast_mul]
    rw [<-Rat.divInt_mul_divInt]
    rw [<-Rat.mkRat_eq_divInt, <-Rat.mkRat_eq_divInt]
    rw [Rat.mkRat_self, Rat.mkRat_self]

-- The product of two irrational numbers is irrational.
example: ∃(x: ℝ) (r: ℚ), Irrational x ∧ r = x * x:= by
    use √2, 2
    exact ⟨irrational_sqrt_two, (Real.mul_self_sqrt zero_le_two).symm⟩
    -- If you were to unfold this, it might look something like this:
    -- apply And.intro
    -- exact irrational_sqrt_two
    -- rw [Real.mul_self_sqrt zero_le_two]
    -- rfl

-- For all integers n, if n is divisible by 4 then n^2 is divisible by 4.
example (n : ℤ): 4 ∣ n → 4 ∣ n ^ 2 := by
    intro four_divides
    rw [pow_two]
    rw [dvd_iff_exists_eq_mul_left] at four_divides ⊢
    rcases four_divides with ⟨m, four_divides⟩
    rw [four_divides]
    use m * 4 * m
    rw [<-mul_assoc]


-- For all integers n, if n^2 is divisible by 4 then n is divisible by 4.
example: ∃n: ℤ, 4 ∣ n ^ 2 ∧ ¬4 ∣ n := by
    use 2
    exact ⟨by rfl, by norm_num⟩
