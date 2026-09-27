from pathlib import Path
import hashlib,json,subprocess,re,datetime,importlib.util
ROOT=Path('/Users/takshkothari/Downloads/collatz')
P=ROOT/'ProofAtlasAttack'; OUT=ROOT/'output/pdf/syracuse-uniform-floor'
spec=importlib.util.spec_from_file_location('audit',P/'scripts/verify.py'); audit=importlib.util.module_from_spec(spec); spec.loader.exec_module(audit)
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
report={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'in_progress','scope':'uniform Syracuse atom theorem and consolidated appendix'}
try:
 sources=list((P/'CollatzTargetDensity').glob('*.lean'))
 manifest=json.loads((audit.VENDOR/'source-manifest.json').read_text())
 for ent in manifest['source_files']:
  p=audit.VENDOR/ent['path']
  assert sha(p)==ent['sha256'], f'Vendor mismatch: {p}'
  sources.append(p)
 sources.append(OUT/'SyracuseUniformFloor.lean')
 for p in sources:
  assert not audit.ESCAPES.search(audit.without_comments(p.read_text())),f'Proof escape: {p}'
 before={str(p.relative_to(ROOT)):sha(p) for p in sources}
 report['upstream_sources_checked']=len(manifest['source_files'])
 report['source_files_scanned']=len(sources)
 report['lean_toolchain']=(P/'lean-toolchain').read_text().strip()
 deps=json.loads((audit.VENDOR/'lake-manifest.json').read_text())['packages']
 report['dependency_revisions']={}
 for d in deps:
  rev=subprocess.check_output(['git','-C',str(audit.VENDOR/'.lake/packages'/d['name']),'rev-parse','HEAD'],text=True).strip()
  assert rev==d['rev'],d['name']
  report['dependency_revisions'][d['name']]=rev
 commands=[(['lake','--rehash','build','+CollatzTargetDensity.SyracuseCylinderSpread:olean'],'theorem-build.log'),(['lake','env','lean',str(OUT/'SyracuseUniformFloor.lean')],'appendix-lean.log')]
 report['commands']=[]
 for cmd,log in commands:
  with (OUT/log).open('w') as f:
   r=subprocess.run(cmd,cwd=P,stdout=f,stderr=subprocess.STDOUT)
  report['commands'].append({'argv':cmd,'exit_code':r.returncode,'log':log})
  assert r.returncode==0,log
 txt=(OUT/'appendix-lean.log').read_text()
 name='CollatzTargetDensity.SyracuseMinorant.syracuse_uniform_atom_lower_bound'
 match=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",txt,re.S)
 assert match,'Missing endpoint axiom evidence'
 axs=sorted(x.strip() for x in match[1].split(','))
 assert set(axs)<=audit.ALLOWED,axs
 report['endpoint']=name; report['axioms']=axs
 assert all(sha(ROOT/f)==h for f,h in before.items()),'Sources changed during verification'
 report['source_sha256']=before
 report['appendix_sha256']=sha(OUT/'SyracuseUniformFloor.lean')
 report['status']='verified'
except Exception as e:
 report['status']='failed'; report['error']=str(e)
finally:
 report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
 print(report['status'],report.get('error',''),flush=True)
 if report['status']!='verified': raise SystemExit(1)
