# Statement comparison draft — not an issued statement

No signatories, issued date, or independent review are asserted.

Source: the full local JSP-000301 description and review notes, which limit
the entry to the yes/no question and exclude the separate counting problem.

The intended definitions are: `Prime p` means p ≥ 2 and every positive proper
divisor is 1; `Powerful n` means n > 0 and every prime divisor p of n satisfies
p² | n; `Square n` means there exists a natural number a with a*a = n.
Natural square roots cover integer squares because a negative integer and
its absolute value have the same square.

The target theorem supplies n = 12167 and proves:

    n > 0 ∧ Powerful n ∧ Powerful (n+1) ∧ ¬ Square n ∧ ¬ Square (n+1).

The corresponding final theorem negates exactly:

    ∀ n : Nat, n > 0 → Powerful n → Powerful (n+1) → Square n ∨ Square (n+1).

The positivity inside `Powerful` is redundant with the original positive
integer domain, not an extra restriction on the original question. Any
bounded finite computation used internally must be connected by proved
lemmas to the unbounded prime and square quantifiers. A bounded test alone
would not be an equivalent statement. Definitions, proof source, and actual
compiler evidence must be reviewed before issuing a signed formal statement.
