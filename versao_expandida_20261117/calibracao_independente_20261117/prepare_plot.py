from pathlib import Path
import csv,collections,math
import numpy as np
p=Path(__file__).resolve().parent;g=collections.defaultdict(list)
for x in csv.DictReader((p/'studies.csv').open()):g[(x['model'],int(x['ncal']),x['contrast'])].append(x)
rows=[]
for (model,n,contrast),data in g.items():
 for method in ('raw','point'):
  a=np.array([float(r[method]) for r in data]);mu=a.mean();se=a.std(ddof=1)/math.sqrt(len(a))
  rows.append(dict(model=model,ncal=n,contrast=contrast,method=method,mean=mu,lo=mu-1.96*se,hi=mu+1.96*se,truth=data[0]['truth']))
with (p/'plot_estimates.csv').open('w',newline='') as f:
 w=csv.DictWriter(f,fieldnames=rows[0].keys());w.writeheader();w.writerows(rows)
