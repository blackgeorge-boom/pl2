import sys
import requests
import urllib
import urllib2
import random
import hashlib
import binascii

def gen_all_hex():
    i = 0
    while i < 16**64:
        yield "{:064X}".format(i)
        i += 1

def get_magic(hex_str):
    data = binascii.a2b_hex(hex_str)
    output = hashlib.sha256(data).hexdigest()
    data = binascii.a2b_hex(output)
    output = hashlib.sha256(data).hexdigest()
    return output[0 : 4]

url = sys.argv[1]

s = requests.Session()

r = s.get(url)
myfile = r.content

lines = myfile.splitlines()
for line in lines:
    line = line.lstrip()
    tokens = line.split()
    if (line.startswith("<span class=\"question\">")):
        magic = (tokens[5])[0:4]
        break
        
print 'Magic is : ' + magic

#print get_magic(hex_str)

for hex_str in gen_all_hex():
    if (get_magic(hex_str) == magic) :
        print 'Magic is : ' + magic
        values = {'answer': hex_str}
        r = s.post(url, values)
        fp = r.content
        print fp
        break


#r = requests.post(url, data=values)
#print r.content

#data = urllib.urlencode(values)
#req = urllib2.Request(url, data)
#response = urllib2.urlopen(req) 
#the_page = response.read()

#print the_page
