import JSP331

-- Print transitive axioms, including those of the imported analytic proof.
#print axioms MediumPNT
#print axioms Erdos402.erdos_402
#print axioms JSP331.eventual_graham
#print axioms JSP331.sufficiently_large_gcd_bound
#print axioms JSP331.distinct_of_gcd_bound
#print axioms JSP331.sufficiently_large_distinct_gcd_bound

-- Expose all binders and casts for statement review.
set_option pp.all true in
#check JSP331.sufficiently_large_gcd_bound
