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

def extract_magic(hex_str):
    data = binascii.a2b_hex(hex_str)
    output = hashlib.sha256(data).hexdigest()
    data = binascii.a2b_hex(output)
    output = hashlib.sha256(data).hexdigest()
    return output[0 : 4]

def get_magic_and_debt(url, s):

    r = s.get(url)
    html = r.content

    lines = html.splitlines()
    for line in lines:
        line = line.lstrip()
        tokens = line.split()
        if (line.startswith("<span class=\"question\">")):
            magic = (tokens[-1])[0:4]
        if ("owe me" in line):
            debt = (tokens[-1])[:-5]
    
    debt = (debt).translate(None, ',')
    debt = float(debt)
    return (magic, debt)

s = requests.Session()
url = sys.argv[1]

data = get_magic_and_debt(url, s)
magic = data[0]
debt = data[1]
print 'Magic is : ' + magic
print 'Debt is : ', debt

#while debt > 0 :
for bitcoin in gen_all_hex():
        bitcoin_magic = extract_magic(bitcoin)
        if (bitcoin_magic == magic):
            values = {'answer': bitcoin}
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
