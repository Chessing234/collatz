from pathlib import Path
import json,hashlib
root=Path('/Users/takshkothari/Downloads/collatz')
out=root/'output/pdf/syracuse-uniform-floor'
r=json.loads((out/'verification.json').read_text())
assert r['status']=='verified',r
s=(out/'SyracuseUniformFloor.lean').read_text()
assert hashlib.sha256(s.encode()).hexdigest()==r['appendix_sha256']
summary=r'''The theorem-specific reverification completed successfully on 12 September
2026. The owning Lake target built successfully, and a separate Lean invocation
accepted the complete consolidated appendix. Both commands returned exit code
zero. The final theorem's transitive axiom set is exactly
\begin{center}\code{propext}, \code{Classical.choice}, \code{Quot.sound}.\end{center}
No admitted theorem, extra mathematical axiom, or native-evaluation axiom
appeared in that footprint. The source scan covered '''+str(r['source_files_scanned'])+r''' files,
including all '''+str(r['upstream_sources_checked'])+r''' pinned upstream source entries;
all manifest hashes and pinned dependency revisions matched. The scanned
source hashes were unchanged between the start and finish of the check.
This focused verification is recorded in \code{verification.json}, with
\code{theorem-build.log} and \code{appendix-lean.log} alongside this document.
The SHA-256 of the exact appendix source is
\begin{center}\footnotesize\texttt{'''+r['appendix_sha256']+r'''}\end{center}
'''
body=(out/'proof-body.tex').read_text().replace(r'\input{verification-summary.tex}',summary)
body=body.replace(r'\usepackage{bookmark}',r'\usepackage{bookmark,xurl}')
tex=body+r'\begin{Verbatim}[fontsize=\fontsize{8}{10}\selectfont,breaklines=true,breakanywhere=true,numbers=left,numbersep=6pt,xleftmargin=15pt,baselinestretch=1]'+'\n'+s+r'\end{Verbatim}'+'\n'+r'\end{document}'+'\n'
(out/'syracuse-uniform-floor.tex').write_text(tex)
print('Assembled',len(s.splitlines()),'exact Lean lines; appendix SHA256',r['appendix_sha256'])
