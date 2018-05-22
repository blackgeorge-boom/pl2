import sys
import re
import requests
import urllib
import urllib2
import random
import hashlib
import binascii

# 
# This function generates all numbers with 64 hex digits
# from 00...0 to FF...F
#
def gen_all_hex():
    i = 0
    while i < 16**64:
        yield "{:064X}".format(i)
        i += 1

#
# This function gets a supposed bitcoin and extracts
# its magic number and its value.
# The results are returned as a tuple.
#
def extract_magic_and_value(hex_str):
    data = binascii.a2b_hex(hex_str)
    output = hashlib.sha256(data).hexdigest()
    data = binascii.a2b_hex(output)
    output = hashlib.sha256(data).hexdigest()

    # First 4 hex digits : magic
    # Second 4 hex digits : value
    return (output[0 : 4], output[5 : 9])

#
# This function visits the server through the url with a get method.
# It returns the magic number and the 'debt' of the user of the current session. 
# The session is sent through the "s" argument.
#
def get_magic_and_debt(url, s):

    # HTTP method
    r = s.get(url)
    # HTML code returned
    html = r.content

    magic = ""

    # Examine the html returned to extract information from the session.
    lines = html.splitlines()
    for line in lines:

        # Remove whitespaces from the left
        line = line.lstrip()
        # Tokenize line
        tokens = line.split()

        # The magic code is the last word of a <span class="question"
        # Also we need to remove the </span> letters from the last word
        if (line.startswith("<span class=\"question\">")):
            magic = (tokens[-1])[0:4]
        # Debt can be found in the line which says "owe me"
        # Also need to extract extra letters from the last word.
        if ("owe me" in line):
            debt = (tokens[-1])[:-5]
    
    # Remove commas (if any) from float representation of debt
    debt = (debt).translate(None, ',')
    # Convert debt string to float
    debt = float(debt)
    
    return (magic, debt)

#
# This function visits the server through the url with a post method.
# The session is sent through the "s" argument.
# It also takes as input the bitcoin to be submitted as answer ("values").
# It returns the response the server gave us. We assume that response lies
# within the HTML code <span class="right"> ... </span>
#
def get_post_response(url, s, values):

    response = ""

    # HTTP Method
    r = s.post(url, values)
    # HTML code returned
    html = r.content

    # Examine the html returned to extract information from the session.
    lines = html.splitlines()
    for line in lines:

        # Remove whitespaces from the left
        line = line.lstrip()
        # Tokenize line
        tokens = line.split()

        # Find the appropriate line, and get rid off the HTML tags using a regex.
        if (line.startswith("<span class=\"right\">")):
            response = re.sub(r'<[^>]*>', '', line)
            break
    
    return response

# Get current session
s = requests.Session()
# Get url from input arguments
url = sys.argv[1]

data = get_magic_and_debt(url, s)
magic = data[0]
debt = data[1]

# Rounds starts from 1
counter = 1
# Continue playing until you owe nothing
while debt > 0 :

    print 'Round', counter, 'magic code: ', magic

    # Find a valid bitcoin, that corresponds to the magic code,
    # using a brute force method.
    for bitcoin in gen_all_hex():
        
            # Extract the magic number from the supposed bitcoin
            bitcoin_data = extract_magic_and_value(bitcoin)
            bitcoin_magic = bitcoin_data[0]

            # if you find a valid bitcoin post it to the server and 
            # get the response back. The bitcoin is valid, 
            # so you need to extract its value also. 
            # Break the for loop.
            if (bitcoin_magic == magic):
                
                values = {'answer': bitcoin}
                response = get_post_response(url, s, values)
                
                bitcoin_value = int(bitcoin_data[1], 16)
                # Convert float value to eurocents.
                bitcoin_value = bitcoin_value / float(100)
                break
            
    # Print what you found
    print bitcoin, bitcoin_value
    print response
    
    # Prepare for the next round
    data = get_magic_and_debt(url, s)
    magic = data[0]
    debt = data[1]
    counter += 1
