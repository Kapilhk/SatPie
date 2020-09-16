# SatPie
## SAT solver based on CDCL in Python
(Easy to Understand - Highly Commented Code)
Features:
1. Conflict Driven Clause Learning
2. Clever Heuristics - VSIDS
3. 2 - Literal watch advanced data structure
4. Random restarts with restart probability decay



### Test & Benchmark Results:
<pre>
Comparison with Edusat:
---------------------------------------------------------------------------------------------------
|        Files :        bmc-2.cnf   | bmc-7.cnf | unsat3.cnf | par8.cnf | aim-50 | aim100 | zebra |
| ------------------- | ----------- | --------- | ---------- | -------- | ------ | ------ | ----- |
| Variables:          | 2810        | 8710      | 13         | 64       | 50     | 100    | 155   |
| SATPIE              | 15.5        | 24.1      | 0.001      | 0.014    | 0.015  | 0.013  | 0.016 |
| Edusat              | 0.26        | 0.324     | 0.15       | 0.014    | 0.031  | 0.013  | 0.4   |
</pre>


### Status:
#### -> The correctness of the SAT Solver has been verified through some of the Benchmarks from various sources. 
#### -> The Solver performs excellently for variables ≈ till 2000, even better than EduSat in some cases.
#### -> The performance starts degrading for very large instances which can be optimized further in future work by learned clause deletion and    Unique Implication Point based clause learning.
### -> Random Restart Probabilty can be adjusted to optimize performance for larger instances.
