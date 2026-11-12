"""Read-only cleanup discovery shared by the one-shot controllers."""


def function_exists(call, name):
    marker = None
    seen = set()
    while True:
        page = call('lambda', 'list-functions', **({'Marker': marker} if marker else {}))
        if any(f['FunctionName'] == name for f in page.get('Functions', [])):
            return True
        marker = page.get('NextMarker')
        if not marker:
            return False
        if marker in seen:
            raise ValueError('Lambda listing repeated a pagination marker; cleanup is unverified')
        seen.add(marker)
