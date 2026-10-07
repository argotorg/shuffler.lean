from pathlib import Path
import hashlib,json,sys
root=Path('spikes/clight-permute').resolve()
sys.path.insert(0,str(root/'tests/equiv-alive2'))
from program_symbols import check_modules
here=Path(__file__).resolve().parent
source=root/'tests/results/extended-2026-10-06/retained-exploration-audit.json'
retained=json.loads(source.read_text())
records=[]
for index,item in enumerate(retained['cases']):
    manifest=root/item['manifest']
    case=manifest.parent/item['case']
    destination=here/str(index)
    destination.mkdir()
    report=check_modules([case/'core.bc',case/'oracle.bc',manifest.parent/'runtime.bc'],destination/'program-symbols.json')
    assert report['pass'],(item,report)
    records.append({'manifest':item['manifest'],'case':item['case'],'symbols':report})
result={'source_audit_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'checker_sha256':hashlib.sha256((root/'tests/equiv-alive2/program_symbols.py').read_bytes()).hexdigest(),
    'case_count':len(records),'cases':records}
assert len(records)==167
output=root/'tests/results/extended-2026-10-06/retained-symbols-audit.json'
with output.open('x') as f:
    f.write(json.dumps(result,indent=2)+'\n')
print('All',len(records),'retained program-module sets pass the KLEE control-symbol check')
