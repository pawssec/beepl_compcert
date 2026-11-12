"""Build a declarative VSIX without npm, downloads, or executable extension code."""
import json
from pathlib import Path
import zipfile
from xml.etree import ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
pkg = json.loads((ROOT / 'package.json').read_text())
ns = 'http://schemas.microsoft.com/developer/vsx-schema/2011'
ET.register_namespace('', ns)
def element(parent, tag, attrs=None, text=None):
    node = ET.SubElement(parent, '{'+ns+'}'+tag, attrs or {})
    node.text = text
    return node
manifest = ET.Element('{'+ns+'}PackageManifest', {'Version':'2.0.0'})
metadata = element(manifest, 'Metadata')
element(metadata, 'Identity', {'Language':'en-US','Id':pkg['name'],
        'Version':pkg['version'], 'Publisher':pkg['publisher']})
element(metadata, 'DisplayName', text=pkg['displayName'])
element(metadata, 'Description', {'{http://www.w3.org/XML/1998/namespace}space':'preserve'},pkg['description'])
element(metadata, 'Categories', text=','.join(pkg['categories']))
properties = element(metadata, 'Properties')
element(properties, 'Property', {'Id':'Microsoft.VisualStudio.Code.Engine','Value':pkg['engines']['vscode']})
element(properties, 'Property', {'Id':'Microsoft.VisualStudio.Code.ExtensionKind','Value':'ui'})
installation = element(manifest, 'Installation')
element(installation, 'InstallationTarget', {'Id':'Microsoft.VisualStudio.Code'})
element(manifest, 'Dependencies')
assets = element(manifest, 'Assets')
for kind,path in [('Microsoft.VisualStudio.Code.Manifest','package.json'),('Microsoft.VisualStudio.Services.Content.Details','README.md')]:
    element(assets, 'Asset', {'Type':kind,'Path':'extension/'+path,'Addressable':'true'})
files = ['package.json','language-configuration.json','syntaxes/beepl.tmLanguage.json','snippets/beepl.json','README.md']
for path in files:
    if path.endswith('.json'): json.loads((ROOT/path).read_text())
output = ROOT / 'dist' / f"{pkg['name']}-{pkg['version']}.vsix"
output.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(output,'w',zipfile.ZIP_DEFLATED) as archive:
    archive.writestr('extension.vsixmanifest',ET.tostring(manifest,encoding='utf-8',xml_declaration=True))
    archive.writestr('[Content_Types].xml', '<?xml version="1.0"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="json" ContentType="application/json"/><Default Extension="md" ContentType="text/markdown"/><Default Extension="vsixmanifest" ContentType="text/xml"/></Types>')
    for path in files: archive.write(ROOT/path,'extension/'+path)
with zipfile.ZipFile(output) as archive:
    assert archive.testzip() is None
print(output)
