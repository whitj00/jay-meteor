
/*
 *  jssha256 version 0.1  -  Copyright 2006 B. Poettering
 *
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 *  02111-1307 USA
 */

/*
 * http://point-at-infinity.org/jssha256/
 *
 * This is a JavaScript implementation of the SHA256 secure hash function
 * and the HMAC-SHA256 message authentication code (MAC).
 *
 * The routines' well-functioning has been verified with the test vectors 
 * given in FIPS-180-2, Appendix B and IETF RFC 4231. The HMAC algorithm 
 * conforms to IETF RFC 2104. 
 *
 * The following code example computes the hash value of the string "abc".
 *
 *    SHA256_init();
 *    SHA256_write("abc");
 *    digest = SHA256_finalize();  
 *    digest_hex = array_to_hex_string(digest);
 * 
 * Get the same result by calling the shortcut function SHA256_hash:
 * 
 *    digest_hex = SHA256_hash("abc");
 * 
 * In the following example the calculation of the HMAC of the string "abc" 
 * using the key "secret key" is shown:
 * 
 *    HMAC_SHA256_init("secret key");
 *    HMAC_SHA256_write("abc");
 *    mac = HMAC_SHA256_finalize();
 *    mac_hex = array_to_hex_string(mac);
 *
 * Again, the same can be done more conveniently:
 * 
 *    mac_hex = HMAC_SHA256_MAC("secret key", "abc");
 *
 * Note that the internal state of the hash function is held in global
 * variables. Therefore one hash value calculation has to be completed 
 * before the next is begun. The same applies the the HMAC routines.
 *
 * Report bugs to: jssha256 AT point-at-infinity.org
 *
 */

/******************************************************************************/

/* Two all purpose helper functions follow */

/* string_to_array: convert a string to a character (byte) array */

function string_to_array(str) {
  var len = str.length;
  var res = new Array(len);
  for(var i = 0; i < len; i++)
    res[i] = str.charCodeAt(i);
  return res;
}

/* array_to_hex_string: convert a byte array to a hexadecimal string */

function array_to_hex_string(ary) {
  var res = "";
  for(var i = 0; i < ary.length; i++)
    res += SHA256_hexchars[ary[i] >> 4] + SHA256_hexchars[ary[i] & 0x0f];
  return res;
}

/******************************************************************************/

/* The following are the SHA256 routines */

/* 
   SHA256_init: initialize the internal state of the hash function. Call this
   function before calling the SHA256_write function.
*/

 var SHA256_buf = new Array();
  var SHA256_len = 0;
var SHA256_H = new Array();

SHA256_init = function SHA256_init() {	
  SHA256_H = new Array(0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19);
	
  SHA256_buf = new Array();
  SHA256_len = 0;
}

/*
   SHA256_write: add a message fragment to the hash function's internal state. 
   'msg' may be given as string or as byte array and may have arbitrary length.

*/

function SHA256_write(msg) {	
  if (typeof(msg) == "string")
    SHA256_buf = SHA256_buf.concat(string_to_array(msg));
  else
    SHA256_buf = SHA256_buf.concat(msg);
                    
  for(var i = 0; i + 64 <= SHA256_buf.length; i += 64)
    SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf.slice(i, i + 64));
        
  SHA256_buf = SHA256_buf.slice(i);
        
  SHA256_len += msg.length;
}

/*
   SHA256_finalize: finalize the hash value calculation. Call this function
   after the last call to SHA256_write. An array of 32 bytes (= 256 bits) 
   is returned.
*/

function SHA256_finalize() {
  SHA256_buf[SHA256_buf.length] = 0x80;

  if (SHA256_buf.length > 64 - 8) {
    for(var i = SHA256_buf.length; i < 64; i++)
      SHA256_buf[i] = 0;
    SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf);
    SHA256_buf.length = 0;
  }

  for(var i = SHA256_buf.length; i < 64 - 5; i++)
    SHA256_buf[i] = 0;
  SHA256_buf[59] = (SHA256_len >>> 29) & 0xff;
  SHA256_buf[60] = (SHA256_len >>> 21) & 0xff;
  SHA256_buf[61] = (SHA256_len >>> 13) & 0xff;
  SHA256_buf[62] = (SHA256_len >>> 5) & 0xff;
  SHA256_buf[63] = (SHA256_len << 3) & 0xff;
  SHA256_Hash_Byte_Block(SHA256_H, SHA256_buf);

  var res = new Array(32);
  for(var i = 0; i < 8; i++) {
    res[4 * i + 0] = SHA256_H[i] >>> 24;
    res[4 * i + 1] = (SHA256_H[i] >> 16) & 0xff;
    res[4 * i + 2] = (SHA256_H[i] >> 8) & 0xff;
    res[4 * i + 3] = SHA256_H[i] & 0xff;
  }

  delete SHA256_H;
  delete SHA256_buf;
  delete SHA256_len;
  
  return res;
}

/*
   SHA256_hash: calculate the hash value of the string or byte array 'msg' 
   and return it as hexadecimal string. This shortcut function may be more 
   convenient than calling SHA256_init, SHA256_write, SHA256_finalize 
   and array_to_hex_string explicitly.
*/

function SHA256_hash(msg, no_hex) {
  var res;
  SHA256_init();
   
  SHA256_write(msg);
  
  res = SHA256_finalize();
    
  if (no_hex) {
	  return res;
  }
  
  return array_to_hex_string(res);
}

/******************************************************************************/

/* The following are the HMAC-SHA256 routines */

/*
   HMAC_SHA256_init: initialize the MAC's internal state. The MAC key 'key'
   may be given as string or as byte array and may have arbitrary length.
*/

function HMAC_SHA256_init(key) {
  if (typeof(key) == "string")
    HMAC_SHA256_key = string_to_array(key);
  else
    HMAC_SHA256_key = new Array().concat(key);

  if (HMAC_SHA256_key.length > 64) {
    SHA256_init();
    SHA256_write(HMAC_SHA256_key);
    HMAC_SHA256_key = SHA256_finalize();
  }

  for(var i = HMAC_SHA256_key.length; i < 64; i++)
    HMAC_SHA256_key[i] = 0;
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] ^=  0x36;
  SHA256_init();
  SHA256_write(HMAC_SHA256_key);
}

/*
   HMAC_SHA256_write: process a message fragment. 'msg' may be given as 
   string or as byte array and may have arbitrary length.
*/

function HMAC_SHA256_write(msg) {
  SHA256_write(msg);
}

/*
   HMAC_SHA256_finalize: finalize the HMAC calculation. An array of 32 bytes
   (= 256 bits) is returned.
*/

function HMAC_SHA256_finalize() {
  var md = SHA256_finalize();
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] ^= 0x36 ^ 0x5c;
  SHA256_init();
  SHA256_write(HMAC_SHA256_key);
  SHA256_write(md);
  for(var i = 0; i < 64; i++)
    HMAC_SHA256_key[i] = 0;
  delete HMAC_SHA256_key;
  return SHA256_finalize();
}

/*
   HMAC_SHA256_MAC: calculate the HMAC value of message 'msg' under key 'key'
   (both may be of type string or byte array); return the MAC as hexadecimal 
   string. This shortcut function may be more convenient than calling 
   HMAC_SHA256_init, HMAC_SHA256_write, HMAC_SHA256_finalize and 
   array_to_hex_string explicitly.
*/

function HMAC_SHA256_MAC(key, msg) {
  var res;
  HMAC_SHA256_init(key);
  HMAC_SHA256_write(msg);
  res = HMAC_SHA256_finalize();
  return array_to_hex_string(res);
}

/******************************************************************************/

/* The following lookup tables and functions are for internal use only! */

SHA256_hexchars = new Array('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 
  'a', 'b', 'c', 'd', 'e', 'f');

SHA256_K = new Array(
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 
);

function SHA256_sigma0(x) {
  return ((x >>> 7) | (x << 25)) ^ ((x >>> 18) | (x << 14)) ^ (x >>> 3);
}

function SHA256_sigma1(x) {
  return ((x >>> 17) | (x << 15)) ^ ((x >>> 19) | (x << 13)) ^ (x >>> 10);
}

function SHA256_Sigma0(x) {
  return ((x >>> 2) | (x << 30)) ^ ((x >>> 13) | (x << 19)) ^ 
    ((x >>> 22) | (x << 10));
}

function SHA256_Sigma1(x) {
  return ((x >>> 6) | (x << 26)) ^ ((x >>> 11) | (x << 21)) ^ 
    ((x >>> 25) | (x << 7));
}

function SHA256_Ch(x, y, z) {
  return z ^ (x & (y ^ z));
}

function SHA256_Maj(x, y, z) {
  return (x & y) ^ (z & (x ^ y));
}

function SHA256_Hash_Word_Block(H, W) {	
  for(var i = 16; i < 64; i++)
    W[i] = (SHA256_sigma1(W[i - 2]) +  W[i - 7] + 
      SHA256_sigma0(W[i - 15]) + W[i - 16]) & 0xffffffff;
  var state = new Array().concat(H);
    
  for(var i = 0; i < 64; i++) {
    var T1 = state[7] + SHA256_Sigma1(state[4]) + 
      SHA256_Ch(state[4], state[5], state[6]) + SHA256_K[i] + W[i];
    var T2 = SHA256_Sigma0(state[0]) + SHA256_Maj(state[0], state[1], state[2]);
    state.pop();
    state.unshift((T1 + T2) & 0xffffffff);
    state[4] = (state[4] + T1) & 0xffffffff;
  }
    
  for(var i = 0; i < 8; i++)
    H[i] = (H[i] + state[i]) & 0xffffffff;
}

function SHA256_Hash_Byte_Block(H, w) {	
  var W = new Array(16);
  for(var i = 0; i < 16; i++)
    W[i] = w[4 * i + 0] << 24 | w[4 * i + 1] << 16 | 
      w[4 * i + 2] << 8 | w[4 * i + 3];
      
  SHA256_Hash_Word_Block(H, W);
}
/*
 * jQuery.ajaxMultiQueue - A queue for multiple concurrent ajax requests
 * (c) 2013 Amir Grozki
 * Dual licensed under the MIT and GPL licenses.
 *
 * Based on jQuery.ajaxQueue
 * (c) 2011 Corey Frang
 *
 * Requires jQuery 1.5+
 */
(function($) {
	$.ajaxMultiQueue = function(n) {
		return new MultiQueue(~~n);
	};

	function MultiQueue(number) {
		var queues, i,
			current = 0;

		if (!queues) {
			queues = new Array(number);

			for (i = 0; i < number; i++) {
				queues[i] = $({});
			}
		}

		function queue(ajaxOpts) {
			var jqXHR,
				dfd = $.Deferred(),
				promise = dfd.promise();

			queues[current].queue(doRequest);
			current = (current + 1) % number;

			function doRequest(next) {
				if (ajaxOpts.currentPage && ajaxOpts.currentPage != NRS.currentPage) {
					next();
				} else if (ajaxOpts.currentSubPage && ajaxOpts.currentSubPage != NRS.currentSubPage) {
					next();
				} else {
					jqXHR = $.ajax(ajaxOpts);

					jqXHR.done(dfd.resolve)
						.fail(dfd.reject)
						.then(next, next);
				}
			}

			return promise;
		};

		return {
			queue: queue
		};
	}

})(jQuery);

var Jay = {};

	Jay.commonNodes = ["69.163.40.132", "jnxt.org","nxt.noip.me","23.88.59.40","162.243.122.251"];
	Jay.commonTestnetNodes = ["localhost"];

	Jay.msTimeout = 1000;

	Jay.requestMethods = {};
	Jay.requestMethods.single = 0;
	Jay.requestMethods.fastest = 1;
	Jay.requestMethods.validate = 2;
	Jay.requestMethods.cautious = 3;
	Jay.requestMethods.default = Jay.requestMethods.fastest;
	Jay.requestMethod = Jay.requestMethods.default;

	Jay.req = $.ajaxMultiQueue(6);

	Jay.singleNode = "";
	Jay.bestNodes = [];
	Jay.isTestnet = false;

	Jay.queue = function(node, parameters, onSuccess, onFailure)
	{
		var obj = {};
		obj.url = Jay.resolveNode(node);
		obj.data = parameters;
		obj.beforeSend = function(jqxhr, settings) {
			jqxhr.node = node;
			jqxhr.parameters = parameters;
		};
		obj.method = 'POST';
		obj.success = onSuccess;
		if(onFailure != undefined) obj.error = onFailure;
		else obj.error = onSuccess;
		obj.timeout = Jay.msTimeout;
		Jay.req.queue(obj);
	}

	Jay.setNode = function(nodeName)
	{
		Jay.singleNode = nodeName;
	}

	Jay.setRequestMethod = function(requestMethod)
	{
		Jay.requestMethod = requestMethod;
	}

	Jay.resolveNode = function(nodeName)
	{
		var name = "http://";
		name += nodeName;
		if(Jay.isTestnet) name += ":6876";
		else name += ":7876";
		name += "/nxt";
		return name;
	}

	Jay.nodeScan = function(complete)
	{
		var counter = 0;
		for(var a=0;a<Jay.commonNodes.length;a++)
		{
			Jay.queue(Jay.commonNodes[a], {"requestType":"getTime"}, function(resp, status, xhr) {
				if(status == "success")
				{
					Jay.bestNodes.push(xhr.node);
				}
				counter++;
				if(counter == Jay.commonNodes.length)
				{
					complete();
				}
			});
		}
	}

	Jay.request = function(requestType, parameters, onSuccess, onFailure, requestMethod)
	{
		if(requestMethod == undefined) requestMethod = Jay.requestMethod;
		parameters["requestType"] = requestType;

		if(requestMethod == Jay.requestMethods.single)
		{
			var useNode = Jay.singleNode;
			Jay.queue(useNode, parameters, onSuccess, onFailure);
		}
		else if(requestMethod == Jay.requestMethods.fastest)
		{
			if(Jay.bestNodes.length == 0)
			{
					Jay.nodeScan(function() {
						Jay.queue(Jay.bestNodes[0], parameters, onSuccess, onFailure);
					});
			}
			else
			{
				Jay.queue(Jay.bestNodes[0], parameters, onSuccess, onFailure);
			}
		}
		else if(requestMethod == Jay.requestMethods.validate)
		{
			var vld = [];
			for(var a=0;a<3;a++)
			{
				Jay.queue(Jay.bestNodes[a], parameters, function(resp, status, xhr) {
				    try {
				        vld.push(JSON.parse(resp));
				    }
				    catch (err) {
				        onFailure({ "error": "Unable to Validate" }, "error", xhr);
				    }
					if(vld.length == 3)
					{
						// compare
						if(Jay.objectCompare(vld[0], vld[1]))
						{
							onSuccess(vld[0], "success", xhr);
						}
						else if(Jay.objectCompare(vld[1], vld[2]))
						{
							onSuccess(vld[1], "success", xhr);
						}
						else if(Jay.objectCompare(vld[0], vld[2]))
						{
							onSuccess(vld[2], "success", xhr);
						}
						else
						{
							onFailure({"error":"Unable to Validate"}, "error", xhr);
						}
					}
				});
			}
		}
	}

	Jay.objectCompare = function(o1, o2, params)
	{
		if(params === undefined)
		{
			// search for all things
			o1.requestProcessingTime = 0;
			o2.requestProcessingTime = 0;
			return objectEquals(o1, o2);
		}
		else
		{
			// compare only the objects in params..
			for(var b=0;b<params.length;b++)
			{
				if(params[b] in o1 && params[b] in o2)
				{
					if(typeof(o1[params[b]]) == Object)
					{
						if(JSON.stringify(o1[params[b]]) != JSON.stringify(o2[params[b]])) return false;
					}
					else
					{
						if(o1[params[b]] != o[params[b]]) return false;
					}
				}
				else return false;
		 	}
			return true;

		}
	}

	function objectEquals(x, y) {
    'use strict';

    if (x === null || x === undefined || y === null || y === undefined) { return x === y; }
    // after this just checking type of one would be enough
    if (x.constructor !== y.constructor) { return false; }
    // if they are functions they should exactly refer to same one
    if (x instanceof Function) { return x === y; }
    if (x === y || x.valueOf() === y.valueOf()) { return true; }
    if (Array.isArray(x) && x.length !== y.length) { return false; }

    // if they are dates, they must had equal valueOf
    if (x instanceof Date) { return false; }

    // if they are strictly equal, they both need to be object at least
    if (!(x instanceof Object)) { return false; }
    if (!(y instanceof Object)) { return false; }

    // recursive object equality check
    var p = Object.keys(x);
    return Object.keys(y).every(function (i) { return p.indexOf(i) !== -1; }) ?
            p.every(function (i) { return objectEquals(x[i], y[i]); }) :
            false;
	}

	Jay.types = {};
	Jay.subtypes = {};

	Jay.oneNxt = 100000000;	
	Jay.types.payment = 0;
	Jay.types.messaging = 1;
	Jay.types.asset = 2;
	Jay.types.marketplace = 3;
	Jay.types.accountControl = 4;
	Jay.types.monetarySystem = 5;

	Jay.subtypes.ordinaryPayment = 0;
	Jay.subtypes.arbitraryMessage = 0;
	Jay.subtypes.aliasAssignment = 1;
	Jay.subtypes.pollCreation = 2;
	Jay.subtypes.voteCasting = 3;
	Jay.subtypes.hubAnnouncement = 4;
	Jay.subtypes.accountInfo = 5;
	Jay.subtypes.aliasSell = 6;
	Jay.subtypes.aliasBuy = 7;
	Jay.subtypes.aliasDelete = 8;
	Jay.subtypes.assetIssuance = 0;
	Jay.subtypes.assetTransfer = 1;
	Jay.subtypes.askOrderPlacement = 2;
	Jay.subtypes.bidOrderPlacement = 3;
	Jay.subtypes.askOrderCancellation = 4;
	Jay.subtypes.bidOrderCancellation = 5;
	Jay.subtypes.goodsListing = 0;
	Jay.subtypes.goodsDelisting = 1;
	Jay.subtypes.priceChange = 2;
	Jay.subtypes.quantityChange = 3;
	Jay.subtypes.purchase = 4;
	Jay.subtypes.delivery = 5;
	Jay.subtypes.feedback = 6;
	Jay.subtypes.refund = 7;
	Jay.subtypes.balanceLeasing = 0;
	Jay.subtypes.currencyIssuance = 0;
	Jay.subtypes.reserveIncrease = 1;
	Jay.subtypes.reserveClaim = 2;
	Jay.subtypes.currencyTransfer = 3;
	Jay.subtypes.exchangeOffer = 4;
	Jay.subtypes.exchangeBuy = 5;
	Jay.subtypes.exchangeSell = 6;
	Jay.subtypes.currencyMinting = 7;
	Jay.subtypes.currencyDeletion = 8;

	Jay.appendages = {};
	Jay.appendages.none = 0;
	Jay.appendages.message = 1;
	Jay.appendages.encryptedMessage = 2;
	Jay.appendages.publicKeyAnnouncement = 4;
	Jay.appendages.encryptedMessageToSelf = 8;
	Jay.appendages.phasedTransaction = 16;


	Jay.transactionVersion = 1;
	Jay.TRFVersion = 1;
	Jay.genesisRS = "NXT-MRCC-2YLS-8M54-3CMAJ";

	Jay.epoch = 1385294400;

	Jay.getNxtTime = function()
	{
		return Math.floor(Date.now() / 1000) - Jay.epoch;
	}


	Jay.pad = function(length, val) 
	{
    	var array = [];
    	for (var i = 0; i < length; i++) 
    	{
        	array[i] = val;
    	}
    	return array;
	}

	Jay.positiveByteArray = function(byteArray)
	{
		return converters.hexStringToByteArray(converters.byteArrayToHexString(byteArray));
	}

	Jay.rsToBytes = function(rs)
	{
		var rec = new NxtAddress();
		rec.set(rs);
		var recip = (new BigInteger(rec.account_id())).toByteArray().reverse();
		if(recip.length == 9) recip = recip.slice(0, 8);
		while(recip.length < 8) recip = recip.concat(Jay.pad(1, 0));
		return recip;
	}

	Jay.secretPhraseToPublicKey = function(secretPhrase) 
	{
		var secretPhraseBytes = converters.stringToByteArray(secretPhrase);
		var digest = simpleHash(secretPhraseBytes);
		return curve25519.keygen(digest).p;
	}

	Jay.publicKeyToAccountId = function(publicKey, RSFormat)
	{
		var hex = converters.hexStringToByteArray(publicKey);

		_hash.init();
		_hash.update(hex);

		var account = _hash.getBytes();

		account = converters.byteArrayToHexString(account);

		var slice = (converters.hexStringToByteArray(account)).slice(0, 8);

		var accountId = byteArrayToBigInteger(slice).toString();

		if (RSFormat) {
			var address = new NxtAddress();

			if (address.set(accountId)) {
				return address.toString();
			} else {
				return "";
			}
		} else {
			return accountId;
		}
	}

	Jay.numberToBytes = function(num)
	{
		var bytes = (new BigInteger((num).toString())).toByteArray().reverse();
		if(bytes.length == 9) bytes = bytes.slice(0, 8);
		while(bytes.length < 8) bytes = bytes.concat(Jay.pad(1, 0));
		return bytes;
	}

	Jay.createTrfBytes = function(type, subtype, recipient, amount, fee, attachment, appendages)
	{
		var trf = [];
		trf.push(Jay.TRFVersion);
		trf.push(type);
		trf.push((subtype) + (Jay.transactionVersion << 4));
		trf = trf.concat(Jay.rsToBytes(recipient));
		trf = trf.concat(Jay.numberToBytes(Math.round(amount*Jay.oneNxt)));
		trf = trf.concat(Jay.numberToBytes(Math.round(fee*Jay.oneNxt)));
		if(appendages == undefined) trf = trf.concat([0,0,0,0]);
		else trf = trf.concat(appendages.flags);
		if(attachment != undefined) trf = trf.concat(attachment);
		if(appendages != undefined) trf = trf.concat(Jay.combineAppendages(appendages));
		return Jay.positiveByteArray(trf);
	}

	Jay.createTrf = function(type, subtype, recipient, amount, fee, attachment, appendages)
	{
		var trfBytes = Jay.createTrfBytes(type, subtype, recipient, amount, fee, attachment, appendages);
		return Jay.finishTrf(trfBytes);
	}

	Jay.bytesToBigInteger = function(bytes)
	{
		var bi = new BigInteger("0");
		for(var a=0; a<bytes.length; a++)
		{
			bi = bi.multiply(new BigInteger("256"));
			//var term = (new BigInteger(bytes[a].toString())).multiply(multiplier);
			bi = bi.add(new BigInteger(bytes[a].toString()));

		}
		return bi;
	}

	Jay.base62_encode = function(bytes) 
	{
		var value = Jay.bytesToBigInteger(bytes);
	    var buf = "";
	    while ((new BigInteger("0")).compareTo(value) < 0) {
	      	var divRem = value.divideAndRemainder(new BigInteger("62"));
	      	var remainder = divRem[1].intValue();
	      
	      	if (remainder < 10) 
	     	{
	        	buf += String.fromCharCode(remainder + '0'.charCodeAt(0));
	      	}
	      	else if (remainder < 10 + 26) 
	     	{
	      		buf += String.fromCharCode(remainder + 'A'.charCodeAt(0) - 10);
	      	} 
	      	else 
	      	{
	        	buf += String.fromCharCode(remainder + 'a'.charCodeAt(0) - 10 - 26);
	      	}
	      
	      	value = divRem[0];
	    }
	    buf = buf.split("").reverse().join("");
	    return buf;
	  }

	Jay.finishTrf = function(trfBytes)
	{
		return "TX_" + Jay.base62_encode(trfBytes);
	}

	Jay.sendMoney = function(recipient, amount, appendages)
	{
		return Jay.createTrf(Jay.types.payment, Jay.subtypes.ordinaryPayment, recipient, amount, 1, undefined, appendages);
	}

	Jay.sendMessage = function(recipient, message, appendages)
	{
		var appendage = Jay.addAppendage(Jay.appendages.message, message, appendages);
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.arbitraryMessage, recipient, 0, 1, undefined, appendage);
	}

	Jay.setAlias = function(alias, data, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length)
		attachment = attachment.concat(converters.stringToByteArray(alias));
		attachment = attachment.concat(Jay.wordBytes(data.length));
		attachment = attachment.concat(converters.stringToByteArray(data));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasAssignment, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.setAccountInfo = function(name, description, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(name.length);
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.accountInfo, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.sellAlias = function(alias, price, recipient, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(price*Jay.oneNxt)));
		if(recipient == undefined || recipient == "anyone" || recipient == "") return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasSell, [0,0,0,0,0,0,0,0], 0, 1, attachment, appendages);
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasSell, recipient, 0, 1, attachment, appendages);
	}

	Jay.buyAlias = function(alias, amount, recipient, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasBuy, recipient, amount, 1, attachment, appendages);
	}

	Jay.deleteAlias = function(alias)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(alias.length);
		attachment = attachment.concat(converters.stringToByteArray(alias));
		return Jay.createTrf(Jay.types.messaging, Jay.subtypes.aliasDelete, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.issueAsset = function(name, description, quantity, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment.push(name.length);
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(quantity*Math.pow(10,decimals))));
		attachment.push(decimals);
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.assetIssuance, Jay.genesisRS, 0, 1000, attachment, appendages);
	}

	Jay.transferAsset = function(recipient, assetId, quantityQNT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));
		attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.assetTransfer, recipient, 0, 1, attachment, appendages);
	}

	Jay.placeAskOrder = function(assetId, quantityQNT, priceNQT, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));

		if(decimals == undefined || typeof(decimals) != "number")
		{
			attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
			attachment = attachment.concat(Jay.numberToBytes(priceNQT));
			appendages = decimals;
		}
		else
		{
			attachment = attachment.concat(Jay.numberToBytes(Math.round(quantityQNT*Math.pow(10, decimals))));
			attachment = attachment.concat(Jay.numberToBytes(Math.round(priceNQT*Math.pow(10, 8-decimals))));
		}
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.askOrderPlacement, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.placeBidOrder = function(assetId, quantityQNT, priceNQT, decimals, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(assetId));
		
		if(decimals == undefined || typeof(decimals) != "number")
		{
			attachment = attachment.concat(Jay.numberToBytes(quantityQNT));
			attachment = attachment.concat(Jay.numberToBytes(priceNQT));
			appendages = decimals;
		}
		else
		{
			attachment = attachment.concat(Jay.numberToBytes(Math.round(quantityQNT*Math.pow(10, decimals))));
			attachment = attachment.concat(Jay.numberToBytes(Math.round(priceNQT*Math.pow(10, 8-decimals))));
		}
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.bidOrderPlacement, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.cancelAskOrder = function(orderId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(orderId));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.askOrderCancellation, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.cancelBidOrder = function(orderId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(orderId));
		return Jay.createTrf(Jay.types.asset, Jay.subtypes.bidOrderCancellation, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsListing = function(name, description, tags, quantity, price, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.wordBytes(name.length));
		attachment = attachment.concat(converters.stringToByteArray(name));
		attachment = attachment.concat(Jay.wordBytes(description.length));
		attachment = attachment.concat(converters.stringToByteArray(description));
		attachment = attachment.concat(Jay.wordBytes(tags.length));
		attachment = attachment.concat(converters.stringToByteArray(tags));
		attachment = attachment.concat(converters.int32ToBytes(quantity));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(price*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.goodsListing, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsDelisting = function(itemId, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.goodsDelisting, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsPriceChange = function(itemId, newPrice, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(newPrice*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.priceChange, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsQuantityChange = function(itemId, deltaQuantity, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(converters.int32ToBytes(deltaQuantity));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.quantityChange, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsPurchase = function(itemId, quantity, priceNQT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion)
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		attachment = attachment.concat(converters.int32ToBytes(quantity));
		attachment = attachment.concat(Jay.numberToBytes(priceNQT));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.purchase, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsDelivery = function(itemId, discount)
	{
		var attachment = [];
	}

	Jay.dgsFeedback = function(itemId, feedback, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(itemId));
		appendages = Jay.addAppendage(Jay.appendages.message, feedback, appendages);
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.feedback, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.dgsRefund = function(purchaseId, refundAmount, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(purchaseId));
		attachment = attachment.concat(Jay.numberToBytes(Math.round(refundAmount*Jay.oneNxt)));
		return Jay.createTrf(Jay.types.marketplace, Jay.subtypes.refund, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.leaseBalance = function(recipient, duration, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.wordBytes(duration));
		return Jay.createTrf(Jay.types.accountControl, Jay.subtypes.balanceLeasing, recipient, 0, 1, attachment, appendages);
	}

	Jay.currencyReserveIncrease = function(currencyId, amountPerUnit, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Math.round(amountPerUnit*Jay.oneNxt));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.reserveIncrease, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.transferCurrency = function(recipient, currencyId, amountQNT, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Jay.numberToBytes(amountQNT));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.currencyTransfer, recipient, 0, 1, attachment, appendages)
	}

	Jay.currencyMint = function(currencyId, nonce, units, counter, appendages)
	{
		var attachment = [];
		attachment.push(Jay.transactionVersion);
		attachment = attachment.concat(Jay.numberToBytes(currencyId));
		attachment = attachment.concat(Jay.numberToBytes(nonce));
		attachment = attachment.concat(Jay.numberToBytes(units));
		attachment = attachment.concat(Jay.numberToBytes(counter));
		return Jay.createTrf(Jay.types.monetarySystem, Jay.subtypes.currencyMinting, Jay.genesisRS, 0, 1, attachment, appendages);
	}

	Jay.wordBytes = function(word)
	{
		return [Math.floor(word%256), Math.floor(word/256)];
	}

	Jay.addAppendage = function(newAppendage, newAppendageData, appendages)
	{
		var flags;
		if(appendages != undefined)
		{
			flags = converters.byteArrayToSignedInt32(appendages.flags);
		}
		else 
		{
			appendages = {};
			flags = 0;
		}

		flags += newAppendage;

		if(newAppendage == Jay.appendages.message)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data.push(0);
			data.push(128);
			data = data.concat(converters.stringToByteArray(newAppendageData));
			appendages.message = data;
		}
		/*else if(newAppendage == Jay.appendages.encryptedMessage)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data = data.concat(converters.stringToByteArray(newAppendageData);
			appendages.encryptedMessage = data;
		}*/
		/*else if(newAppendage == Jay.appendages.encryptedMessageToSelf)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(Jay.wordBytes(newAppendageData.length));
			data = data.concat(converters.stringToByteArray(newAppendageData);
			appendages.encryptedMessageToSelf = data;
		}*/
		if(newAppendage == Jay.appendages.publicKeyAnnouncement)
		{
			var data = [];
			data.push(Jay.transactionVersion);
			data = data.concat(converters.hexStringToByteArray(newAppendageData));
			appendages.publicKeyAnnouncement = data;
		}
		appendages.flags = converters.int32ToBytes(flags);
		return appendages;
	}

	Jay.combineAppendages = function(appendages)
	{
		var data = [];
		if(appendages.message != undefined)
		{
			data = data.concat(appendages.message);
		}		
		if(appendages.encryptedMessage != undefined)
		{
			data = data.concat(appendages.encryptedMessage)
		}
		if(appendages.encryptedMessageToSelf != undefined)
		{
			data = data.concat(appendages.encryptedMessageToSelf)
		}
		if(appendages.publicKeyAnnouncement != undefined)
		{
			data = data.concat(appendages.publicKeyAnnouncement);
		}
		return data;
	}



var _hash = {
		init: SHA256_init,
		update: SHA256_write,
		getBytes: SHA256_finalize
	};

function byteArrayToBigInteger(byteArray, startIndex) {
		var value = new BigInteger("0", 10);
		var temp1, temp2;
		for (var i = byteArray.length - 1; i >= 0; i--) {
			temp1 = value.multiply(new BigInteger("256", 10));
			temp2 = temp1.add(new BigInteger(byteArray[i].toString(10), 10));
			value = temp2;
		}

		return value;
	}

function simpleHash(message) {
		_hash.init();
		_hash.update(message);
		return _hash.getBytes();
	}

var epochNum = 1385294400;
function getPublicKey(secretPhrase)
{
	SHA256_init();
	SHA256_write(converters.stringToByteArray(secretPhrase));
	var ky = converters.byteArrayToHexString(curve25519.keygen(SHA256_finalize()).p);

	return converters.hexStringToByteArray(ky);
}

function toByteArray(long) {
    // we want to represent the input as a 8-bytes array
    var byteArray = [0, 0, 0, 0];

    for ( var index = 0; index < byteArray.length; index ++ ) {
        var byte = long & 0xff;
        byteArray [ index ] = byte;
        long = (long - byte) / 256 ;
    }

    return byteArray;
};

	function toIntVal(byteArray) {
	    // we want to represent the input as a 8-bytes array
	    var intval = 0;

	    for ( var index = 0; index < byteArray.length; index ++ ) {
	    	var byt = byteArray[index] & 0xFF;
	    	var value = byt * Math.pow(256, index);
	    	intval += value;
	    }

	    return intval;
	};

	Jay.signBytes = function(message, secretPhrase) {
		var messageBytes = message;
		var secretPhraseBytes = converters.stringToByteArray(secretPhrase);

		var digest = simpleHash(secretPhraseBytes);
		var s = curve25519.keygen(digest).s;

		var m = simpleHash(messageBytes);
		_hash.init();
		_hash.update(m);
		_hash.update(s);
		var x = _hash.getBytes();

		var y = curve25519.keygen(x).p;

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h = _hash.getBytes();

		var v = curve25519.sign(h, x, s);


		return v.concat(h);
	}

	function areByteArraysEqual(bytes1, bytes2) {
		if (bytes1.length !== bytes2.length)
			return false;

		for (var i = 0; i < bytes1.length; ++i) {
			if (bytes1[i] !== bytes2[i])
				return false;
		}

		return true;
	}

	Jay.verifyBytes = function(signature, message, publicKey) {
		var signatureBytes = signature;
		var messageBytes = message;
		var publicKeyBytes = publicKey;
		var v = signatureBytes.slice(0, 32);
		var h = signatureBytes.slice(32);
		var y = curve25519.verify(v, h, publicKeyBytes);

		var m = simpleHash(messageBytes);

		_hash.init();
		_hash.update(m);
		_hash.update(y);
		var h2 = _hash.getBytes();

		return areByteArraysEqual(h, h2);
	}

	Jay.createToken = function(websiteString, secretPhrase)
	{
		//alert(converters.stringToHexString(websiteString));
		var hexwebsite = converters.stringToHexString(websiteString);
        var website = converters.hexStringToByteArray(hexwebsite);
        var data = [];
        data = website.concat(getPublicKey(secretPhrase));
        var unix = Math.round(+new Date()/1000);
        var timestamp = unix-epochNum;
        var timestamparray = toByteArray(timestamp);
        data = data.concat(timestamparray);

        var token = [];
        token = getPublicKey(secretPhrase).concat(timestamparray);

        var sig = Jay.signBytes(data, secretPhrase);

        token = token.concat(sig);
        var buf = "";

        for (var ptr = 0; ptr < 100; ptr += 5) {

        	var nbr = [];
        	nbr[0] = token[ptr] & 0xFF;
        	nbr[1] = token[ptr+1] & 0xFF;
        	nbr[2] = token[ptr+2] & 0xFF;
        	nbr[3] = token[ptr+3] & 0xFF;
        	nbr[4] = token[ptr+4] & 0xFF;
        	var number = byteArrayToBigInteger(nbr);

            if (number < 32) {
                buf+="0000000";
            } else if (number < 1024) {
                buf+="000000";
            } else if (number < 32768) {
                buf+="00000";
            } else if (number < 1048576) {
                buf+="0000";
            } else if (number < 33554432) {
                buf+="000";
            } else if (number < 1073741824) {
                buf+="00";
            } else if (number < 34359738368) {
                buf+="0";
            }
            buf +=number.toString(32);

        }
        return buf;

    }

	Jay.parseToken = function(tokenString, website)
	{
 		var websiteBytes = converters.stringToByteArray(website);
        var tokenBytes = [];
        var i = 0;
        var j = 0;

        for (; i < tokenString.length; i += 8, j += 5) {

        	var number = new BigInteger(tokenString.substring(i, i+8), 32);
            var part = converters.hexStringToByteArray(number.toRadix(16));

            tokenBytes[j] = part[4];
            tokenBytes[j + 1] = part[3];
            tokenBytes[j + 2] = part[2];
            tokenBytes[j + 3] = part[1];
            tokenBytes[j + 4] = part[0];
        }

        if (i != 160) {
            new Error("tokenString parsed to invalid size");
        }
        var publicKey = [];
        publicKey = tokenBytes.slice(0, 32);
        var timebytes = [tokenBytes[32], tokenBytes[33], tokenBytes[34], tokenBytes[35]];

        var timestamp = toIntVal(timebytes);
        var signature = tokenBytes.slice(36, 100);

        var data = websiteBytes.concat(tokenBytes.slice(0, 36));
       	
        var isValid = Jay.verifyBytes(signature, data, publicKey);

        var ret = {};
        ret.isValid = isValid;
        ret.timestamp = timestamp;
        ret.publicKey = converters.byteArrayToHexString(publicKey);
        ret.accountRS = Jay.publicKeyToAccountId(ret.publicKey, true);

        return ret;

	}
