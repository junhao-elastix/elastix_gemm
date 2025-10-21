# Burst Count Analysis

## First FETCH (Successful)
- Lines requested: 528
- Bursts needed: 528 ÷ 16 = **33 bursts**
- Test output: "✓ Left FETCH completed"
- BRAM writes: [0-527]

**This PROVES: 33 bursts CAN succeed!**

## Second FETCH (Fails)
- Lines requested: 528  
- Bursts needed: 528 ÷ 16 = **33 bursts**
- Actual written: 512 lines = **32 bursts**
- BRAM writes: [528-1039] (should be [528-1055])

## Critical Observation

**If first FETCH completes 33 bursts successfully, why does second FETCH fail at burst 33?**

This means it's NOT:
- ❌ A "33-burst limit" in GDDR6/NoC
- ❌ A general AXI protocol issue

This suggests it IS:
- ✅ Something specific to the SECOND FETCH
- ✅ OR a BRAM write address issue (≥528)
- ✅ OR cumulative state issue
