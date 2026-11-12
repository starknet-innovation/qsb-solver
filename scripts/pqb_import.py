"""Import an attested OCI archive with the host Docker client and check actual runtime content."""
import json
from pathlib import Path
import subprocess
import sys


def verify_runtime(image, config):
    if image['Architecture'] != config['architecture'] or image['Os'] != config['os']:
        raise ValueError('Imported architecture differs')
    if image['RootFS']['Layers'] != config['rootfs']['diff_ids']:
        raise ValueError('Imported rootfs differs')
    for key, value in config['config'].items():
        if image['Config'].get(key) != value:
            raise ValueError('Imported runtime config differs: '+key)
    if image['Config'].get('WorkingDir') != '/opt/qsb-pqb' or image['Config'].get('Cmd') != ['python3','aws_entrypoint.py']:
        raise ValueError('Unexpected PQB runtime command')


def import_image(bundle, results, call=subprocess.run):
    bundle, results = Path(bundle), Path(results)
    identity=json.loads((bundle/'gate/oci-identity.json').read_text())
    config=json.loads((bundle/'image-config.json').read_text())
    done=call(['docker','load','--input',str(bundle/'image.oci.tar'),'--platform','linux/amd64'],
              capture_output=True,text=True,timeout=180)
    (results/'image-import.log').write_text(done.stdout+'\n'+done.stderr)
    done.check_returncode()
    # Store IDs vary across Docker backends. Only inspect concrete loaded references
    # and the exact attested index/platform/config identities; validate actual content.
    refs=[line.split(': ',1)[1] for line in done.stdout.splitlines()
          if line.startswith(('Loaded image ID: ','Loaded image: '))]
    refs += [identity[k] for k in ['imageDigest','platformDigest','configDigest']]
    for ref in dict.fromkeys(refs):
        inspected=call(['docker','inspect',ref],capture_output=True,text=True,timeout=30)
        if inspected.returncode:
            continue
        images=json.loads(inspected.stdout)
        if len(images)!=1:
            raise ValueError('Expected one imported image')
        (results/'image.json').write_text(inspected.stdout)
        verify_runtime(images[0],config)
        call(['docker','tag',ref,'qsb-pqb:final'],capture_output=True,text=True,timeout=30).check_returncode()
        (results/'runtime-identity-check.json').write_text(json.dumps(dict(status='passed',
            imageDigest=identity['imageDigest'],configDigest=identity['configDigest'],
            dockerInspectId=images[0]['Id'],rootfsDiffIdsMatched=True,runtimeConfigMatched=True),indent=2)+'\n')
        return
    raise ValueError('Docker did not expose a verifiable loaded image')


if __name__=='__main__':
    import_image(*sys.argv[1:])
