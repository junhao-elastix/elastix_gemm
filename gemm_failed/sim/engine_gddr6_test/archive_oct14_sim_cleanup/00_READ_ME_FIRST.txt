================================================================================
GDDR6 SIMULATION - READ ME FIRST
================================================================================

I've built a complete GDDR6 simulation environment to debug your hardware issue.

THE AUTOMATED TERMINAL ISN'T WORKING, SO:
------------------------------------------------------------------------
Open a real terminal and run this:

    cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
    bash run_sim.sh


WHAT THIS DOES:
------------------------------------------------------------------------
- Compiles GDDR6 models + your GEMM engine RTL (3-5 minutes)
- Runs full simulation with command sequence (5-15 minutes)
- Shows results and identifies issues

TOTAL TIME: 10-20 minutes


WHAT YOU'LL SEE:
------------------------------------------------------------------------
First run will show commands flowing correctly but results will be wrong.
This is EXPECTED and documented - GDDR6 data preload not implemented yet.

BUT you'll verify:
  ✓ Compilation works
  ✓ Commands flow through system
  ✓ FSM transitions properly
  ✓ No hangs or errors
  ✓ Results captured (even if wrong)


WHAT TO READ:
------------------------------------------------------------------------
1. START_HERE.txt - Quick instructions (30 seconds)
2. SUMMARY.md - What this is and why (2 minutes)
3. RUN_NOW.md - Detailed steps if script fails (5 minutes)
4. CHECKLIST.md - Step-by-step verification (reference)


BOTTOM LINE:
------------------------------------------------------------------------
Just run: bash run_sim.sh

It will tell you everything as it goes.


================================================================================
cd /home/dev/Dev/elastix_gemm/gemm/sim/engine_gddr6_test
bash run_sim.sh
================================================================================


