#!/usr/bin/env python3
"""Recompute the supplementary results using Python 3 standard library only."""
import argparse,csv,json,math
from collections import Counter,defaultdict
from pathlib import Path
from metric_functions import metric_bundle,cluster_bootstrap,permutation_pvalue,holm
ROOT=Path(__file__).resolve().parents[1]

def csvrows(rel):
 with (ROOT/rel).open(encoding='utf-8-sig',newline='') as f:return list(csv.DictReader(f))
def jsonlines(rel):return [json.loads(l) for l in (ROOT/rel).read_text(encoding='utf-8').splitlines() if l.strip()]
def yes(x):return str(x).lower() in {'true','1','yes'}
def close(a,b):assert math.isclose(float(a),float(b),abs_tol=1e-9),(a,b)
def write(out,name,rows):
 with (out/name).open('w',encoding='utf-8',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def rankings(section,anchor,groups):
 refs=csvrows('recommendation/references.csv')
 valid=defaultdict(set)
 for r in refs:
  if r['label']=='VALID' or (r['label']=='CONDITIONAL' and yes(r.get('conditional_satisfied',''))):valid[r['task_id']].add(r['plan_id'])
 T=sorted(t for t in groups if valid[t])
 per=defaultdict(list);hits=defaultdict(dict)
 seen=set()
 for r in jsonlines(section+'/rankings.jsonl'):
  m,t=r['method'],r['task_id'];assert (m,t) not in seen;seen.add((m,t))
  rank=r['ranking'];assert len(rank)==len(set(rank))
  abstained=r['abstained'] or str(r.get('abstain_reason','')).startswith('NOT_AVAILABLE')
  first=next((i+1 for i,p in enumerate(rank) if p in valid[t]),None)
  p1=int(r['top1'] in valid[t]) if r['top1'] else 0
  s3=int(bool(set(r['top3']) & valid[t]))
  if abstained:p1,s3,first=0,0,None
  row=dict(in_T=t in T,p1_hit=p1,s3_hit=s3,first_valid_rank=first)
  per[m].append(row);hits[m][t]=p1
  # Check regenerated scores against the exported per-task results below.
  r['_scores']=(p1,s3,first)
 bundles={m:metric_bundle(per[m]) for m in per}
 expected={r['method']:r for r in csvrows(section+'/comparison.csv')}
 rows=[]
 for m in per:
  b=bundles[m];e=expected[m]
  assert len(per[m])==100
  for k in ['p1_n','s3_n','p1','s3','mrr']:close(b[k],e[k])
  rows.append(dict(method=m,task_count=len(per[m]),T_n=b['n'],p1_n=b['p1_n'],p1=b['p1'],s3_n=b['s3_n'],s3=b['s3'],mrr=b['mrr']))
 group=lambda t:groups[t]['leakage_group'] or t
 # The original helper uses B4 as the anchor label for both evaluations.
 mapped={('B4' if m==anchor else m):h for m,h in hits.items()}
 ci,delta=cluster_bootstrap(T,mapped,group,10000,20261011)
 pvals={m:permutation_pvalue(T,hits[anchor],hits[m],group,20261011)[0] for m in hits if m!=anchor}
 adj=holm(pvals)
 diffs=[dict(comparison=anchor+' - '+m,delta_p1=bundles[anchor]['p1']-bundles[m]['p1'],ci95=delta[m],permutation_p=pvals[m],holm_adj_p=adj[m]) for m in pvals]
 expected_name='baseline_differences.csv' if section=='recommendation' else 'module_differences.csv'
 expected_diffs=csvrows(section+'/'+expected_name)
 for d,e in zip(diffs,expected_diffs):close(d['holm_adj_p'],e['holm_adj_p'])
 for row in rows:row['p1_ci95']=ci['B4' if row['method']==anchor else row['method']]
 return rows,diffs

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'recomputed');args=ap.parse_args();out=args.output;out.mkdir(parents=True,exist_ok=True)
 groups={r['task_id']:r for r in csvrows('recommendation/task_groups.csv')}
 for section,anchor in [('recommendation','B4'),('ablation','FULL')]:
  rows,diffs=rankings(section,anchor,groups);write(out,section+'.csv',rows);write(out,section+'_differences.csv',diffs)
 pairs=csvrows('paired/pair_results.csv');old=csvrows('paired/original_b4_results.csv')
 assert len(pairs)==60 and len({r['pair_slot'] for r in pairs})==60
 assert len(csvrows('paired/side_results.csv'))==120
 assert len(csvrows('paired/target_bindings.csv'))==43
 hits={r['task_id']:int(r['result_class']=='MATCHED') for r in pairs}
 ci,_=cluster_bootstrap(list(hits),{'B4':hits},lambda t:groups[t]['leakage_group'] or t,10000,20261011)
 paired=[]
 for label,rows in [('Original B4',old),('B4+ALIGN',pairs)]:
  selected=[r for r in rows if r['result_class']=='MATCHED']
  real=[r for r in rows if r['kind']=='REAL'];bench=[r for r in rows if r['kind']!='REAL']
  paired.append(dict(method=label,N=len(rows),successes=len(selected),success_rate=len(selected)/len(rows),real_n=len(real),real_successes=sum(r['result_class']=='MATCHED' for r in real),benchmark_n=len(bench),benchmark_successes=sum(r['result_class']=='MATCHED' for r in bench),successful_real_projects=len({r['project'] for r in selected if r['kind']=='REAL'}),ci95=ci['B4'] if label=='B4+ALIGN' else ''))
 write(out,'paired.csv',paired)
 receipts=jsonlines('timing/task_receipts.jsonl')+jsonlines('timing/aligned_task_receipts.jsonl')
 by=defaultdict(list)
 for r in receipts:by[r['method']].append(r)
 expected={r['method']:r for r in csvrows('timing/execution_comparison.csv')}
 execution=[]
 for m,rows in by.items():
  assert len(rows)==100
  n=sum(r['terminal']=='END_TO_END_SUCCESS' for r in rows)
  close(n,expected[m]['S_num'])
  execution.append(dict(method=m,N=len(rows),end_to_end_successes=n,end_to_end_rate=n/len(rows)))
 write(out,'execution.csv',execution)
 physical={r['run_key']:r for r in jsonlines('timing/physical_runs.jsonl')}
 prep=json.loads((ROOT/'timing/input_prep_timing.json').read_text())['sides']
 expected_cost={r['method']:r for r in csvrows('timing/five_method_costs.csv')}
 base_costs=[]
 for m,rows in by.items():
  if m=='B4+ALIGN':continue
  keys={part.split(':',1)[1] for r in rows for part in r['run_keys'].split(';') if ':' in part}
  keys&=physical.keys()
  identities={r.get(side+'_input_identity') for r in rows for side in ['buggy','fixed'] if r.get(side+'_input_identity')}
  tool=round(sum(physical[k]['duration_s'] for k in sorted(keys) if physical[k].get('duration_s') is not None),3)
  preparation=round(sum(prep[k] for k in sorted(identities) if prep.get(k) is not None),3)
  total=round(sum(physical[k]['duration_s'] for k in sorted(keys) if physical[k].get('duration_s') is not None)+sum(prep[k] for k in sorted(identities) if prep.get(k) is not None),3)
  close(total,expected_cost[m]['total_including_prep_s'])
  base_costs.append(dict(method=m,tool_seconds=tool,input_prep_seconds=preparation,known_machine_seconds=total))
 write(out,'five_method_costs.csv',base_costs)
 ledger=csvrows('timing/cost_dedup_ledger.csv');buckets=defaultdict(float);seen=set()
 for r in ledger:
  if yes(r['counted_in_total']):
   assert r['ledger_key'] not in seen;seen.add(r['ledger_key'])
   if r['duration_s'] not in {'','null','None'}:buckets[r['operation_kind']]+=float(r['duration_s'])
 tool=round(buckets['B4_TOOL_RUN'],3);preparation=round(buckets['INPUT_PREP'],3)
 checker=round(buckets['ALIGN_RULE_CHECK'],6);ast=round(buckets['AST_PARSE'],6)
 increment=round(checker+ast,6);total=round(tool+preparation+increment,6)
 recorded={(r['view'],r['metric']):r for r in csvrows('timing/aligned_costs.csv')}
 close(increment,recorded['ALIGNMENT_INCREMENT','known_increment_seconds']['value']);close(total,recorded['EXTENDED_TOTAL','known_total_seconds']['value'])
 cost=[dict(metric='base_known_machine_seconds',value=round(tool+preparation,3)),dict(metric='alignment_increment_seconds',value=increment),dict(metric='aligned_known_machine_seconds',value=total),dict(metric='relative_increment_percent',value=100*increment/(tool+preparation))]
 write(out,'aligned_costs.csv',cost)
 summary={'recommendation_records':len(jsonlines('recommendation/rankings.jsonl')),'ablation_records':len(jsonlines('ablation/rankings.jsonl')),'pairs':len(pairs),'paired_successes':sum(hits.values()),'paired_ci95':ci['B4'],'paired_distribution':dict(Counter(r['result_class'] for r in pairs)),'known_machine_seconds':total,'alignment_increment_seconds':increment}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));print('Recomputed tables:',out)
if __name__=='__main__':main()
