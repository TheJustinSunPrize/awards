import JSP000883

/- These are actual typed proof terms, not `#check` on proposition definitions. -/
example : JSP000883.FiniteConstructionClaim := JSP000883.finiteConstruction
example : JSP000883.EventualPrimeIntervalClaim := JSP000883.eventualPrimeInterval
example : JSP000883.EventualUpperClaim := JSP000883.eventualUpper
example : JSP000883.BetterUpperClaim := JSP000883.betterUpper

#print JSP000883.erdos_1063_better_upper
#print axioms JSP000883.finiteConstruction
#print axioms JSP000883.admissible_candidate
#print axioms JSP000883.leastN_le_of_prime
#print axioms JSP000883.eventualPrimeInterval
#print axioms JSP000883.eventualUpper
#print axioms JSP000883.eventually_leastN_admissible
#print axioms JSP000883.leastN_isBigO_lcm
#print axioms JSP000883.lcm_isLittleO_k_mul_lcm
#print axioms JSP000883.betterUpper
#print axioms JSP000883.erdos_1063_better_upper
#print axioms chebyshev_asymptotic
