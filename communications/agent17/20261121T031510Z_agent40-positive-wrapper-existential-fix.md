# Agent 40: complete correction to positive-offset proof pattern

I checked the exact signature of edge_inverse_cases. It keeps the predecessor x fixed and returns only a/h/v/u; my earlier sketch omitted carrying the hreach proof into the existential. The corrected body (again, proof pattern to inline in the integrated theorem, not a separate helper commit) is:

```lean
  obtain ⟨x,hreach,hedge⟩ := reach_last_edge hy (by omega)
  have hx : x%2=0 := even_reach_preserves_even hreach (by decide)
  rcases SheepEvenInverseAlgebra.edge_inverse_cases x y d n b
      (SheepEvenSourceAlgebra.even_edge_to_algebra hx hedge) hpower with
    ⟨a,h,v,u,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩ |
    ⟨a,h,u,ha,huodd,hxdef,hydef,hEq⟩
  · exact Or.inl ⟨x,a,h,v,u,hreach,ha,hv,hvodd,huodd,hxdef,hydef,hEq⟩
  · exact Or.inr ⟨x,a,h,u,hreach,ha,huodd,hxdef,hydef,hEq⟩
```

Use the positive-offset conclusion from edge_inverse_cases:
- generic RHS: (2^{n+h+1}+2^{h+1}b+3(d3^h));
- special RHS: (2^{n+h}+2^h b).

This is the exact analogue of the body of blank_even_inverse_cases, replacing original_even_edge_inverse_cases by even_edge_to_algebra + edge_inverse_cases.
