# Exact replay record

Campaign: `one-tenth-endpoint-geometry-20260905-b1`, coupled-arcs lane.
The lane admission was written before the first arithmetic execution.

## First checkpoint

- Normal replay: exit 0; all seven fixed controls PASS.
- `/usr/bin/time` reported wall `0.02` seconds, user `0.01`, system `0.00`.
- No timeout, search, additional fixture, arithmetic dependency, or geometry gap
  was encountered. The only remaining admitted execution is optimized replay
  of the same seven controls, with the same 60-second hard process limit.
- Current cumulative arithmetic wall: `0.02` seconds (timer resolution).

Command (run from the assigned worktree):

```sh
env PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 /usr/bin/time -f 'wall_seconds=%e cpu_user=%U cpu_system=%S' timeout 60 /home/argustest/.hermes/hermes-agent/venv/bin/python -B research/one-tenth/endpoint-geometry-b1/coupled-arcs/replay.py
```

Output:

```text
PASS 1: (m,R,r)=(1,2,1/3); pi*old=1/4; pi*joint=1/4
PASS 2: (m,R,r)=(1,2,1/2); pi*old=1/4; pi*joint=1/4
PASS 3: (m,R,r)=(1,2,3/4); pi*old=1/8; pi*joint=1/4
PASS 4: (m,R,r)=(1,2,7/8); pi*old=1/16; pi*joint=1/8
PASS 5: (m,R,r)=(1,2,1); pi*old=0; pi*joint=0
PASS 6: (m,R,r)=(1,1,3/4); pi*old=1/4; pi*joint=1/4
PASS 7: r_*=1089/1600; pi*terminal_payment_gain=21141/6400000
PASS: 7 fixed rational controls; no search; geometry proof is in PROOF.md
```

The exact gain `21141/6400000` concerns the **pi-scaled finite-high terminal
payment with the old fixed price**. It is not a gain in the minimum of all
branch payments, and must not be added to the accepted universal floor.

## Final checkpoint

Optimized replay used the identical command with `python -B -O`. It exited 0
and produced the identical eight PASS lines above. Its timer reported wall
`0.02` seconds, user `0.02`, system `0.00`. All seven controls are explicit
runtime checks, so `-O` cannot disable them.

Cumulative reported arithmetic wall: `0.02 s + 0.02 s`; two sequential runs,
seven distinct preregistered controls, no timeout and no further arithmetic
execution. Success stop reached. The exact rational comparison and strict
improvement formula passed; the universal geometry remains a human proof
awaiting parent review.

Status: **completed**. No accepted source or global floor was changed.
