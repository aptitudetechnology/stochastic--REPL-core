# Google Deep Research Prompt: DTQC + Olfaction MVP

Please conduct focused research to answer ONE core question with maximum speed and clarity:

---

## Core Question

**Can I test DTQC principles (quasiperiodic forcing at 24h + 24.84h timescales) on olfactory systems using existing computational models within 30 days, and would this be MORE tractable than the cyanobacteria photosynthesis approach?**

---

## Essential Information Only (MVP Scope)

### 1. Does Olfaction Have Circadian Coupling? (10 min search)

**Must answer:**
- ✅ YES/NO: Do olfactory receptors or sensitivity show circadian variation?
- ✅ Which organisms? (need at least ONE with published models)
- ✅ Is the effect size large enough to matter? (>10% variation)

**Search terms:**
- "circadian olfactory sensitivity"
- "olfactory receptor circadian expression"

**Deliverable:** 
- One paragraph + 2-3 key citations
- Decision: IS there circadian coupling to leverage?

---

### 2. Is There a Ready-Made Computational Model? (10 min search)

**Must find:**
- ✅ Existing computational model of olfactory system (preferably open-source code)
- ✅ Model includes time-dependent processes (not just static input→output)
- ✅ Model has tunable parameters that could be optimized
- ✅ Model runs in reasonable time (<1 hour per simulation)

**Search terms:**
- "computational model olfactory receptor Python"
- "olfactory bulb neural network code"
- "C elegans chemotaxis simulation GitHub"
- "Drosophila olfactory circuit model"

**Deliverable:**
- Name of model + link to code/paper
- Brief description of what it simulates
- Estimated effort to implement DTQC forcing
- Decision: CAN I use this immediately?

---

### 3. What's the Optimization Problem? (5 min search)

**Must identify:**
- ✅ What parameter would I optimize? (receptor sensitivity? neural weights? decision threshold?)
- ✅ What's the fitness function? (detection accuracy? discrimination performance? energy efficiency?)
- ✅ Is this comparable to the cyanobacteria fitness (carbon fixation)?

**Deliverable:**
- One-sentence optimization problem statement
- Example: "Optimize receptor sensitivity parameters to maximize odor discrimination accuracy under noisy conditions"

---

### 4. Comparison to Cyanobacteria Approach (5 min analysis)

**Must compare:**

| Factor | Cyanobacteria | Olfaction | Winner |
|--------|---------------|-----------|---------|
| Circadian coupling exists? | ✅ Yes (strong) | ? | ? |
| Model availability? | ✅ BioXen ready | ? | ? |
| Clear optimization problem? | ✅ Carbon fixation | ? | ? |
| Computational cost? | ~2h per run | ? | ? |
| Novelty of application? | Moderate | ? | ? |

**Deliverable:**
- Fill in the "?" cells
- Recommendation: SWITCH or STICK with cyanobacteria?

---

## GO/NO-GO Decision Criteria

### ✅ GO (switch to olfaction) IF:
1. Strong circadian coupling exists (>15% variation)
2. Ready-made model available (can download and run today)
3. Clear optimization problem (comparable to photosynthesis)
4. Equal or faster than cyanobacteria (~2h per simulation)
5. Offers unique advantage (better data, more applications, etc.)

### ❌ NO-GO (stick with cyanobacteria) IF:
1. Weak/no circadian coupling (<10% variation)
2. No existing model (would need to build from scratch)
3. Unclear what to optimize
4. Much slower than cyanobacteria (>5h per simulation)
5. No clear advantage over original plan

### ⚠️ MAYBE (needs deeper investigation) IF:
- Circadian coupling exists but model needs adaptation
- Interesting application but higher implementation risk

---

## Minimal Deliverable Format

### Part 1: Quick Facts (bullet points only)
- Circadian coupling in olfaction: YES/NO + strength
- Best organism for modeling: [NAME]
- Available model: [NAME/LINK] or "None found"
- Optimization target: [ONE SENTENCE]
- Computational cost estimate: [X hours per run]

### Part 2: GO/NO-GO Recommendation (1 paragraph)
- Clear recommendation with reasoning
- Biggest advantage if GO
- Biggest risk if GO

### Part 3: If GO - Next Steps (3 bullet points)
- Download/implement [MODEL NAME]
- Add DTQC forcing to [PARAMETER]
- Test with [QUICK PILOT SETUP]

### Part 4: If NO-GO - Why Stick with Cyanobacteria (1 paragraph)

---

## Time Limit

**Target research time:** 30 minutes maximum

**Rationale:** This is a quick feasibility check, not a comprehensive review. If it takes >30 min to find basic information, that's a signal that olfaction might be harder than cyanobacteria.

---

## Success Metric

**This MVP is successful if it provides:**
- ✅ Clear YES/NO answer within 30 minutes
- ✅ Enough information to make switching decision TODAY
- ✅ Specific next action (either "download this model" or "proceed with cyanobacteria")

**This MVP fails if:**
- ❌ Answer is "maybe, needs more research"
- ❌ Takes >30 min without clear conclusion
- ❌ Identifies olfaction is interesting but requires building everything from scratch

---

## The One Question to Answer

**After 30 minutes of research, can you confidently say:**

*"Yes, I can test DTQC on [SPECIFIC OLFACTORY MODEL] by [SPECIFIC METHOD] and get results within 30 days, and this is better than cyanobacteria because [SPECIFIC REASON]"*

**OR**

*"No, stick with cyanobacteria because olfaction requires [MISSING PIECE] which would add weeks to the timeline"*

---

**Focus:** Speed over comprehensiveness. Deep research can come AFTER we know if this pivot makes sense.