#!/usr/bin/env python3
"""Kernel first-event certificates and exact finite exception exploration."""
import subprocess
from audit_barrier_kernel import ROOT,check_axioms,check_false_certificates
from check_proof_escapes import violations
from explore_product_descent_delay import investigate

def main():
    name='Collatz.Exploration.ProductDelayCertificates'
    source=ROOT/'Collatz/Exploration/ProductDelayCertificates.lean'
    assert not violations(source.read_text())
    subprocess.run(['lake','build',name],cwd=ROOT,check=True)
    report=investigate(1000000,1000)
    assert report['missing']==[]
    assert report['matched']==999995
    assert [(r['source'],r['first_descent'],r['first_certificate']) for r in report['delayed']]==[
        (27,59,65),(31,56,61),(47,54,55),(63,54,56)]
    axioms=check_axioms(source,name)
    bad=check_false_certificates(name,[
        'set_option maxRecDepth 10000 in\nexample : Collatz.Exploration.ProductDelayCertificates.FirstCertificate 27 59 := by decide\n',
        'set_option maxRecDepth 10000 in\nexample : Collatz.Exploration.ProductDelayCertificates.FirstDescent 27 65 := by decide\n',
    ])
    print(f'999999 sources explored; {axioms} theorem footprints; {bad} false first-event controls rejected')

if __name__=='__main__':main()
