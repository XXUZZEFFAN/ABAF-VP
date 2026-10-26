"""Metric and statistical functions used in the recorded evaluation."""
import itertools
import random

def metric_bundle(per_task):
    """per_task: list of dicts with in_T, p1_hit, s3_hit, first_valid_rank."""
    T = [r for r in per_task if r["in_T"]]
    n = len(T)
    if n == 0:
        return {"n": 0, "p1_n": 0, "p1": None, "s3_n": 0, "s3": None, "mrr": None}
    p1 = sum(r["p1_hit"] for r in T)
    s3 = sum(r["s3_hit"] for r in T)
    mrr = sum(1.0 / r["first_valid_rank"] if r["first_valid_rank"] else 0.0 for r in T)
    return {"n": n, "p1_n": p1, "p1": p1 / n, "s3_n": s3, "s3": s3 / n, "mrr": mrr / n}

def cluster_bootstrap(tasks_T, per_method_hits, group_of, resamples, seed):
    """Percentile 95% CIs for each method P@1 and for B4 minus each baseline.
    tasks_T: ordered task ids in T. per_method_hits: method -> {tid: 0/1}."""
    rng = random.Random(seed)
    clusters = {}
    for t in tasks_T:
        clusters.setdefault(group_of(t), []).append(t)
    keys = sorted(clusters)
    n = len(tasks_T)
    methods = sorted(per_method_hits)
    if n == 0:
        return ({m: None for m in methods}, {m: None for m in methods if m != "B4"})
    if resamples <= 0:
        raise ValueError("bootstrap resamples must be positive")
    samples = {m: [] for m in methods}
    deltas = {b: [] for b in methods if b != "B4"}
    for _ in range(resamples):
        draw = [rng.choice(keys) for _ in keys]
        idx = [t for k in draw for t in clusters[k]]
        p1 = {}
        for m in methods:
            p1[m] = sum(per_method_hits[m][t] for t in idx) / len(idx)
            samples[m].append(p1[m])
        for b in deltas:
            deltas[b].append(p1["B4"] - p1[b])

    def ci(xs):
        xs = sorted(xs)
        return (xs[int(0.025 * len(xs))], xs[min(len(xs) - 1, int(0.975 * len(xs)))])
    return ({m: ci(samples[m]) for m in methods},
            {b: ci(deltas[b]) for b in deltas})

def permutation_pvalue(tasks_T, hits_b4, hits_base, group_of, seed, mc=100000):
    """Paired cluster sign-flip test on per-task P@1 differences (two-sided).
    Exact enumeration when 2^clusters is small, else Monte Carlo."""
    clusters = {}
    for t in tasks_T:
        clusters.setdefault(group_of(t), []).append(t)
    keys = sorted(clusters)
    d = {t: hits_b4[t] - hits_base[t] for t in tasks_T}
    n = len(tasks_T)
    if n == 0:
        return None, "NA_EMPTY_DENOMINATOR"
    obs = sum(d.values()) / n
    k = len(keys)
    if 2 ** k <= 200000:
        cnt = 0
        total = 2 ** k
        for signs in itertools.product((1, -1), repeat=k):
            s = sum(sg * sum(d[t] for t in clusters[g]) for sg, g in zip(signs, keys))
            cnt += abs(s / n) >= abs(obs) - 1e-12
        return cnt / total, f"exact 2^{k}"
    rng = random.Random(seed)
    cnt = 0
    for _ in range(mc):
        s = sum(rng.choice((1, -1)) * sum(d[t] for t in clusters[g]) for g in keys)
        cnt += abs(s / n) >= abs(obs) - 1e-12
    return (cnt + 1) / (mc + 1), f"monte_carlo {mc}"

def holm(pvals):
    """Holm-adjusted p-values. pvals: dict label -> p."""
    items = sorted((p, l) for l, p in pvals.items())
    m = len(items)
    adj, running = {}, 0.0
    for i, (p, l) in enumerate(items):
        running = max(running, min(1.0, (m - i) * p))
        adj[l] = running
    return adj
