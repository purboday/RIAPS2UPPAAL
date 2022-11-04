import xml.etree.ElementTree as ET

path = ''
filename = 'RelayManager.xml'

tree = ET.parse(path+filename)
root = tree.getroot()
print(root.tag)

for child in root.findall('./template'):
    for grandchild in child:
        print(grandchild.tag, grandchild.attrib, grandchild.text)
        for greatgrandchild in grandchild:
            print(greatgrandchild.tag, greatgrandchild.attrib, greatgrandchild.text)
    