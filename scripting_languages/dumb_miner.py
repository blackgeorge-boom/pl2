import sys
import re
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
    return (output[0 : 4], output[5 : 9])


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

def get_post_response(url, s, values):

    r = s.post(url, values)
    html = r.content

    lines = html.splitlines()
    for line in lines:
        line = line.lstrip()
        tokens = line.split()
        if (line.startswith("<span class=\"right\">")):
            response = re.sub(r'<[^>]*>', '', line)
            break
    
    return response


s = requests.Session()
url = sys.argv[1]

data = get_magic_and_debt(url, s)
magic = data[0]
debt = data[1]

counter = 1
while debt > 0 :
    print 'Round', counter, 'magic code: ', magic
    for bitcoin in gen_all_hex():
            bitcoin_data = extract_magic(bitcoin)
            bitcoin_magic = bitcoin_data[0]
            bitcoin_value = int(bitcoin_data[1], 16)
            bitcoin_value = bitcoin_value / float(100)
            if (bitcoin_magic == magic):
                values = {'answer': bitcoin}
                response = get_post_response(url, s, values)
                #print fp
                break
    print bitcoin, bitcoin_value
    print response
    data = get_magic_and_debt(url, s)
    magic = data[0]
    debt = data[1]
    counter += 1




#r = requests.post(url, data=values)
#print r.content

#data = urllib.urlencode(values)
#req = urllib2.Request(url, data)
#response = urllib2.urlopen(req) 
#the_page = response.read()

#print the_page
