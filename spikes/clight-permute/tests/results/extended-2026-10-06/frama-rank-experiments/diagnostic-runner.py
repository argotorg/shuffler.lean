from pathlib import Path
import argparse,hashlib,json,shutil,subprocess
p=argparse.ArgumentParser()
p.add_argument('--source',type=Path,required=True)
p.add_argument('--name',required=True)
p.add_argument('--properties')
p.add_argument('--rte',action='store_true')
p.add_argument('--provers',default='tip,z3,cvc5')
p.add_argument('--debug',action='store_true')
a=p.parse_args()
root=Path('spikes/clight-permute').resolve()
out=root/'build/frama-c'/a.name
out.mkdir(exist_ok=False)
source=a.source.resolve()
shutil.copy2(source,out/'input.c')
config=root/'build/frama-c/memory-resumed-9/why3.conf'
command=[shutil.which('frama-c'),'-wp-why3-config',str(config),'-wp-no-why3-detect','-wp-prover',a.provers,'-machdep','x86_64','-cpp-extra-args=-I'+str(root),str(out/'input.c'),'-then','-wp','-wp-model','Typed+ref','-wp-split','-wp-par','4','-wp-timeout','10','-wp-cache','none','-wp-proof-trace','-wp-out',str(out/'obligations'),'-wp-session',str(out/'session'),'-wp-report-json',str(out/'goals.json'),'-wp-print']
command[command.index('-then')+1:command.index('-then')+1]=['-wp-why3-config',str(config),'-wp-no-why3-detect','-wp-prover',a.provers]
if a.rte:command+=['-wp-rte','-rte-initialized=permute']
if a.debug:command+=['-wp-debug','1','-wp-msg-key','tactical']
if a.properties:command+=['-wp-prop',a.properties]
manifest={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'config':str(config),'config_sha256':hashlib.sha256(config.read_bytes()).hexdigest(),'command':command}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with (out/'wp.log').open('w') as log:
    result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
print('process exit',result.returncode)
if (out/'goals.json').exists():
    goals=json.loads((out/'goals.json').read_text())
    print('goals',len(goals),'valid',sum(g.get('verdict')=='valid' for g in goals))
    print('pending',[(g['goal'],g.get('verdict')) for g in goals if g.get('verdict')!='valid'])
