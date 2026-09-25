"""Generate the consumer descriptor from the tagged commit and pushed image digest."""
import json,os,pathlib,re

def descriptor(commit,digest):
    if not re.fullmatch('[0-9a-f]{40}',commit):raise ValueError('Invalid solver commit')
    if not re.fullmatch('sha256:[0-9a-f]{64}',digest):raise ValueError('Invalid registry digest')
    return {'schemaVersion':2,'id':'qsb-ranked-v2-'+commit[:12]+'-'+digest[7:19],
      'protocol':'qsb-config-a-v1','generatorCommit':'2c9172051d5c150ef0a994ca6b988a08a3ef9e85',
      'searchVersion':'ranked-v2','solverRepository':'https://github.com/starknet-innovation/qsb-solver',
      'solverCommit':commit,'kernelCommit':'2791ed0588f5014ccd688d48ba5502df2879f2f1',
      'image':'ghcr.io/starknet-innovation/qsb-solver@'+digest}
if __name__=='__main__':
    value=descriptor(os.environ['SOLVER_COMMIT'],os.environ['IMAGE_DIGEST'])
    target=pathlib.Path('release-output');target.mkdir(exist_ok=True)
    (target/'solver.json').write_text(json.dumps(value,indent=2)+'\n')
