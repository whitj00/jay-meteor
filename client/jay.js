/*
CryptoJS v3.1.2
code.google.com/p/crypto-js
(c) 2009-2013 by Jeff Mott. All rights reserved.
code.google.com/p/crypto-js/wiki/License
*/
var CryptoJS = CryptoJS || function(u, p) {
		var d = {}, l = d.lib = {}, s = function() {}, t = l.Base = {
				extend: function(a) {
					s.prototype = this;
					var c = new s;
					a && c.mixIn(a);
					c.hasOwnProperty("init") || (c.init = function() {
						c.$super.init.apply(this, arguments)
					});
					c.init.prototype = c;
					c.$super = this;
					return c
				},
				create: function() {
					var a = this.extend();
					a.init.apply(a, arguments);
					return a
				},
				init: function() {},
				mixIn: function(a) {
					for (var c in a) a.hasOwnProperty(c) && (this[c] = a[c]);
					a.hasOwnProperty("toString") && (this.toString = a.toString)
				},
				clone: function() {
					return this.init.prototype.extend(this)
				}
			},
			r = l.WordArray = t.extend({
				init: function(a, c) {
					a = this.words = a || [];
					this.sigBytes = c != p ? c : 4 * a.length
				},
				toString: function(a) {
					return (a || v).stringify(this)
				},
				concat: function(a) {
					var c = this.words,
						e = a.words,
						j = this.sigBytes;
					a = a.sigBytes;
					this.clamp();
					if (j % 4)
						for (var k = 0; k < a; k++) c[j + k >>> 2] |= (e[k >>> 2] >>> 24 - 8 * (k % 4) & 255) << 24 - 8 * ((j + k) % 4);
					else if (65535 < e.length)
						for (k = 0; k < a; k += 4) c[j + k >>> 2] = e[k >>> 2];
					else c.push.apply(c, e);
					this.sigBytes += a;
					return this
				},
				clamp: function() {
					var a = this.words,
						c = this.sigBytes;
					a[c >>> 2] &= 4294967295 <<
						32 - 8 * (c % 4);
					a.length = u.ceil(c / 4)
				},
				clone: function() {
					var a = t.clone.call(this);
					a.words = this.words.slice(0);
					return a
				},
				random: function(a) {
					for (var c = [], e = 0; e < a; e += 4) c.push(4294967296 * u.random() | 0);
					return new r.init(c, a)
				}
			}),
			w = d.enc = {}, v = w.Hex = {
				stringify: function(a) {
					var c = a.words;
					a = a.sigBytes;
					for (var e = [], j = 0; j < a; j++) {
						var k = c[j >>> 2] >>> 24 - 8 * (j % 4) & 255;
						e.push((k >>> 4).toString(16));
						e.push((k & 15).toString(16))
					}
					return e.join("")
				},
				parse: function(a) {
					for (var c = a.length, e = [], j = 0; j < c; j += 2) e[j >>> 3] |= parseInt(a.substr(j,
						2), 16) << 24 - 4 * (j % 8);
					return new r.init(e, c / 2)
				}
			}, b = w.Latin1 = {
				stringify: function(a) {
					var c = a.words;
					a = a.sigBytes;
					for (var e = [], j = 0; j < a; j++) e.push(String.fromCharCode(c[j >>> 2] >>> 24 - 8 * (j % 4) & 255));
					return e.join("")
				},
				parse: function(a) {
					for (var c = a.length, e = [], j = 0; j < c; j++) e[j >>> 2] |= (a.charCodeAt(j) & 255) << 24 - 8 * (j % 4);
					return new r.init(e, c)
				}
			}, x = w.Utf8 = {
				stringify: function(a) {
					try {
						return decodeURIComponent(escape(b.stringify(a)))
					} catch (c) {
						throw Error("Malformed UTF-8 data");
					}
				},
				parse: function(a) {
					return b.parse(unescape(encodeURIComponent(a)))
				}
			},
			q = l.BufferedBlockAlgorithm = t.extend({
				reset: function() {
					this._data = new r.init;
					this._nDataBytes = 0
				},
				_append: function(a) {
					"string" == typeof a && (a = x.parse(a));
					this._data.concat(a);
					this._nDataBytes += a.sigBytes
				},
				_process: function(a) {
					var c = this._data,
						e = c.words,
						j = c.sigBytes,
						k = this.blockSize,
						b = j / (4 * k),
						b = a ? u.ceil(b) : u.max((b | 0) - this._minBufferSize, 0);
					a = b * k;
					j = u.min(4 * a, j);
					if (a) {
						for (var q = 0; q < a; q += k) this._doProcessBlock(e, q);
						q = e.splice(0, a);
						c.sigBytes -= j
					}
					return new r.init(q, j)
				},
				clone: function() {
					var a = t.clone.call(this);
					a._data = this._data.clone();
					return a
				},
				_minBufferSize: 0
			});
		l.Hasher = q.extend({
			cfg: t.extend(),
			init: function(a) {
				this.cfg = this.cfg.extend(a);
				this.reset()
			},
			reset: function() {
				q.reset.call(this);
				this._doReset()
			},
			update: function(a) {
				this._append(a);
				this._process();
				return this
			},
			finalize: function(a) {
				a && this._append(a);
				return this._doFinalize()
			},
			blockSize: 16,
			_createHelper: function(a) {
				return function(b, e) {
					return (new a.init(e)).finalize(b)
				}
			},
			_createHmacHelper: function(a) {
				return function(b, e) {
					return (new n.HMAC.init(a,
						e)).finalize(b)
				}
			}
		});
		var n = d.algo = {};
		return d
	}(Math);
(function() {
	var u = CryptoJS,
		p = u.lib.WordArray;
	u.enc.Base64 = {
		stringify: function(d) {
			var l = d.words,
				p = d.sigBytes,
				t = this._map;
			d.clamp();
			d = [];
			for (var r = 0; r < p; r += 3)
				for (var w = (l[r >>> 2] >>> 24 - 8 * (r % 4) & 255) << 16 | (l[r + 1 >>> 2] >>> 24 - 8 * ((r + 1) % 4) & 255) << 8 | l[r + 2 >>> 2] >>> 24 - 8 * ((r + 2) % 4) & 255, v = 0; 4 > v && r + 0.75 * v < p; v++) d.push(t.charAt(w >>> 6 * (3 - v) & 63));
			if (l = t.charAt(64))
				for (; d.length % 4;) d.push(l);
			return d.join("")
		},
		parse: function(d) {
			var l = d.length,
				s = this._map,
				t = s.charAt(64);
			t && (t = d.indexOf(t), -1 != t && (l = t));
			for (var t = [], r = 0, w = 0; w <
				l; w++)
				if (w % 4) {
					var v = s.indexOf(d.charAt(w - 1)) << 2 * (w % 4),
						b = s.indexOf(d.charAt(w)) >>> 6 - 2 * (w % 4);
					t[r >>> 2] |= (v | b) << 24 - 8 * (r % 4);
					r++
				}
			return p.create(t, r)
		},
		_map: "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
	}
})();
(function(u) {
	function p(b, n, a, c, e, j, k) {
		b = b + (n & a | ~n & c) + e + k;
		return (b << j | b >>> 32 - j) + n
	}

	function d(b, n, a, c, e, j, k) {
		b = b + (n & c | a & ~c) + e + k;
		return (b << j | b >>> 32 - j) + n
	}

	function l(b, n, a, c, e, j, k) {
		b = b + (n ^ a ^ c) + e + k;
		return (b << j | b >>> 32 - j) + n
	}

	function s(b, n, a, c, e, j, k) {
		b = b + (a ^ (n | ~c)) + e + k;
		return (b << j | b >>> 32 - j) + n
	}
	for (var t = CryptoJS, r = t.lib, w = r.WordArray, v = r.Hasher, r = t.algo, b = [], x = 0; 64 > x; x++) b[x] = 4294967296 * u.abs(u.sin(x + 1)) | 0;
	r = r.MD5 = v.extend({
		_doReset: function() {
			this._hash = new w.init([1732584193, 4023233417, 2562383102, 271733878])
		},
		_doProcessBlock: function(q, n) {
			for (var a = 0; 16 > a; a++) {
				var c = n + a,
					e = q[c];
				q[c] = (e << 8 | e >>> 24) & 16711935 | (e << 24 | e >>> 8) & 4278255360
			}
			var a = this._hash.words,
				c = q[n + 0],
				e = q[n + 1],
				j = q[n + 2],
				k = q[n + 3],
				z = q[n + 4],
				r = q[n + 5],
				t = q[n + 6],
				w = q[n + 7],
				v = q[n + 8],
				A = q[n + 9],
				B = q[n + 10],
				C = q[n + 11],
				u = q[n + 12],
				D = q[n + 13],
				E = q[n + 14],
				x = q[n + 15],
				f = a[0],
				m = a[1],
				g = a[2],
				h = a[3],
				f = p(f, m, g, h, c, 7, b[0]),
				h = p(h, f, m, g, e, 12, b[1]),
				g = p(g, h, f, m, j, 17, b[2]),
				m = p(m, g, h, f, k, 22, b[3]),
				f = p(f, m, g, h, z, 7, b[4]),
				h = p(h, f, m, g, r, 12, b[5]),
				g = p(g, h, f, m, t, 17, b[6]),
				m = p(m, g, h, f, w, 22, b[7]),
				f = p(f, m, g, h, v, 7, b[8]),
				h = p(h, f, m, g, A, 12, b[9]),
				g = p(g, h, f, m, B, 17, b[10]),
				m = p(m, g, h, f, C, 22, b[11]),
				f = p(f, m, g, h, u, 7, b[12]),
				h = p(h, f, m, g, D, 12, b[13]),
				g = p(g, h, f, m, E, 17, b[14]),
				m = p(m, g, h, f, x, 22, b[15]),
				f = d(f, m, g, h, e, 5, b[16]),
				h = d(h, f, m, g, t, 9, b[17]),
				g = d(g, h, f, m, C, 14, b[18]),
				m = d(m, g, h, f, c, 20, b[19]),
				f = d(f, m, g, h, r, 5, b[20]),
				h = d(h, f, m, g, B, 9, b[21]),
				g = d(g, h, f, m, x, 14, b[22]),
				m = d(m, g, h, f, z, 20, b[23]),
				f = d(f, m, g, h, A, 5, b[24]),
				h = d(h, f, m, g, E, 9, b[25]),
				g = d(g, h, f, m, k, 14, b[26]),
				m = d(m, g, h, f, v, 20, b[27]),
				f = d(f, m, g, h, D, 5, b[28]),
				h = d(h, f,
					m, g, j, 9, b[29]),
				g = d(g, h, f, m, w, 14, b[30]),
				m = d(m, g, h, f, u, 20, b[31]),
				f = l(f, m, g, h, r, 4, b[32]),
				h = l(h, f, m, g, v, 11, b[33]),
				g = l(g, h, f, m, C, 16, b[34]),
				m = l(m, g, h, f, E, 23, b[35]),
				f = l(f, m, g, h, e, 4, b[36]),
				h = l(h, f, m, g, z, 11, b[37]),
				g = l(g, h, f, m, w, 16, b[38]),
				m = l(m, g, h, f, B, 23, b[39]),
				f = l(f, m, g, h, D, 4, b[40]),
				h = l(h, f, m, g, c, 11, b[41]),
				g = l(g, h, f, m, k, 16, b[42]),
				m = l(m, g, h, f, t, 23, b[43]),
				f = l(f, m, g, h, A, 4, b[44]),
				h = l(h, f, m, g, u, 11, b[45]),
				g = l(g, h, f, m, x, 16, b[46]),
				m = l(m, g, h, f, j, 23, b[47]),
				f = s(f, m, g, h, c, 6, b[48]),
				h = s(h, f, m, g, w, 10, b[49]),
				g = s(g, h, f, m,
					E, 15, b[50]),
				m = s(m, g, h, f, r, 21, b[51]),
				f = s(f, m, g, h, u, 6, b[52]),
				h = s(h, f, m, g, k, 10, b[53]),
				g = s(g, h, f, m, B, 15, b[54]),
				m = s(m, g, h, f, e, 21, b[55]),
				f = s(f, m, g, h, v, 6, b[56]),
				h = s(h, f, m, g, x, 10, b[57]),
				g = s(g, h, f, m, t, 15, b[58]),
				m = s(m, g, h, f, D, 21, b[59]),
				f = s(f, m, g, h, z, 6, b[60]),
				h = s(h, f, m, g, C, 10, b[61]),
				g = s(g, h, f, m, j, 15, b[62]),
				m = s(m, g, h, f, A, 21, b[63]);
			a[0] = a[0] + f | 0;
			a[1] = a[1] + m | 0;
			a[2] = a[2] + g | 0;
			a[3] = a[3] + h | 0
		},
		_doFinalize: function() {
			var b = this._data,
				n = b.words,
				a = 8 * this._nDataBytes,
				c = 8 * b.sigBytes;
			n[c >>> 5] |= 128 << 24 - c % 32;
			var e = u.floor(a /
				4294967296);
			n[(c + 64 >>> 9 << 4) + 15] = (e << 8 | e >>> 24) & 16711935 | (e << 24 | e >>> 8) & 4278255360;
			n[(c + 64 >>> 9 << 4) + 14] = (a << 8 | a >>> 24) & 16711935 | (a << 24 | a >>> 8) & 4278255360;
			b.sigBytes = 4 * (n.length + 1);
			this._process();
			b = this._hash;
			n = b.words;
			for (a = 0; 4 > a; a++) c = n[a], n[a] = (c << 8 | c >>> 24) & 16711935 | (c << 24 | c >>> 8) & 4278255360;
			return b
		},
		clone: function() {
			var b = v.clone.call(this);
			b._hash = this._hash.clone();
			return b
		}
	});
	t.MD5 = v._createHelper(r);
	t.HmacMD5 = v._createHmacHelper(r)
})(Math);
(function() {
	var u = CryptoJS,
		p = u.lib,
		d = p.Base,
		l = p.WordArray,
		p = u.algo,
		s = p.EvpKDF = d.extend({
			cfg: d.extend({
				keySize: 4,
				hasher: p.MD5,
				iterations: 1
			}),
			init: function(d) {
				this.cfg = this.cfg.extend(d)
			},
			compute: function(d, r) {
				for (var p = this.cfg, s = p.hasher.create(), b = l.create(), u = b.words, q = p.keySize, p = p.iterations; u.length < q;) {
					n && s.update(n);
					var n = s.update(d).finalize(r);
					s.reset();
					for (var a = 1; a < p; a++) n = s.finalize(n), s.reset();
					b.concat(n)
				}
				b.sigBytes = 4 * q;
				return b
			}
		});
	u.EvpKDF = function(d, l, p) {
		return s.create(p).compute(d,
			l)
	}
})();
CryptoJS.lib.Cipher || function(u) {
	var p = CryptoJS,
		d = p.lib,
		l = d.Base,
		s = d.WordArray,
		t = d.BufferedBlockAlgorithm,
		r = p.enc.Base64,
		w = p.algo.EvpKDF,
		v = d.Cipher = t.extend({
			cfg: l.extend(),
			createEncryptor: function(e, a) {
				return this.create(this._ENC_XFORM_MODE, e, a)
			},
			createDecryptor: function(e, a) {
				return this.create(this._DEC_XFORM_MODE, e, a)
			},
			init: function(e, a, b) {
				this.cfg = this.cfg.extend(b);
				this._xformMode = e;
				this._key = a;
				this.reset()
			},
			reset: function() {
				t.reset.call(this);
				this._doReset()
			},
			process: function(e) {
				this._append(e);
				return this._process()
			},
			finalize: function(e) {
				e && this._append(e);
				return this._doFinalize()
			},
			keySize: 4,
			ivSize: 4,
			_ENC_XFORM_MODE: 1,
			_DEC_XFORM_MODE: 2,
			_createHelper: function(e) {
				return {
					encrypt: function(b, k, d) {
						return ("string" == typeof k ? c : a).encrypt(e, b, k, d)
					},
					decrypt: function(b, k, d) {
						return ("string" == typeof k ? c : a).decrypt(e, b, k, d)
					}
				}
			}
		});
	d.StreamCipher = v.extend({
		_doFinalize: function() {
			return this._process(!0)
		},
		blockSize: 1
	});
	var b = p.mode = {}, x = function(e, a, b) {
			var c = this._iv;
			c ? this._iv = u : c = this._prevBlock;
			for (var d = 0; d < b; d++) e[a + d] ^=
				c[d]
		}, q = (d.BlockCipherMode = l.extend({
			createEncryptor: function(e, a) {
				return this.Encryptor.create(e, a)
			},
			createDecryptor: function(e, a) {
				return this.Decryptor.create(e, a)
			},
			init: function(e, a) {
				this._cipher = e;
				this._iv = a
			}
		})).extend();
	q.Encryptor = q.extend({
		processBlock: function(e, a) {
			var b = this._cipher,
				c = b.blockSize;
			x.call(this, e, a, c);
			b.encryptBlock(e, a);
			this._prevBlock = e.slice(a, a + c)
		}
	});
	q.Decryptor = q.extend({
		processBlock: function(e, a) {
			var b = this._cipher,
				c = b.blockSize,
				d = e.slice(a, a + c);
			b.decryptBlock(e, a);
			x.call(this,
				e, a, c);
			this._prevBlock = d
		}
	});
	b = b.CBC = q;
	q = (p.pad = {}).Pkcs7 = {
		pad: function(a, b) {
			for (var c = 4 * b, c = c - a.sigBytes % c, d = c << 24 | c << 16 | c << 8 | c, l = [], n = 0; n < c; n += 4) l.push(d);
			c = s.create(l, c);
			a.concat(c)
		},
		unpad: function(a) {
			a.sigBytes -= a.words[a.sigBytes - 1 >>> 2] & 255
		}
	};
	d.BlockCipher = v.extend({
		cfg: v.cfg.extend({
			mode: b,
			padding: q
		}),
		reset: function() {
			v.reset.call(this);
			var a = this.cfg,
				b = a.iv,
				a = a.mode;
			if (this._xformMode == this._ENC_XFORM_MODE) var c = a.createEncryptor;
			else c = a.createDecryptor, this._minBufferSize = 1;
			this._mode = c.call(a,
				this, b && b.words)
		},
		_doProcessBlock: function(a, b) {
			this._mode.processBlock(a, b)
		},
		_doFinalize: function() {
			var a = this.cfg.padding;
			if (this._xformMode == this._ENC_XFORM_MODE) {
				a.pad(this._data, this.blockSize);
				var b = this._process(!0)
			} else b = this._process(!0), a.unpad(b);
			return b
		},
		blockSize: 4
	});
	var n = d.CipherParams = l.extend({
		init: function(a) {
			this.mixIn(a)
		},
		toString: function(a) {
			return (a || this.formatter).stringify(this)
		}
	}),
		b = (p.format = {}).OpenSSL = {
			stringify: function(a) {
				var b = a.ciphertext;
				a = a.salt;
				return (a ? s.create([1398893684,
					1701076831
				]).concat(a).concat(b) : b).toString(r)
			},
			parse: function(a) {
				a = r.parse(a);
				var b = a.words;
				if (1398893684 == b[0] && 1701076831 == b[1]) {
					var c = s.create(b.slice(2, 4));
					b.splice(0, 4);
					a.sigBytes -= 16
				}
				return n.create({
					ciphertext: a,
					salt: c
				})
			}
		}, a = d.SerializableCipher = l.extend({
			cfg: l.extend({
				format: b
			}),
			encrypt: function(a, b, c, d) {
				d = this.cfg.extend(d);
				var l = a.createEncryptor(c, d);
				b = l.finalize(b);
				l = l.cfg;
				return n.create({
					ciphertext: b,
					key: c,
					iv: l.iv,
					algorithm: a,
					mode: l.mode,
					padding: l.padding,
					blockSize: a.blockSize,
					formatter: d.format
				})
			},
			decrypt: function(a, b, c, d) {
				d = this.cfg.extend(d);
				b = this._parse(b, d.format);
				return a.createDecryptor(c, d).finalize(b.ciphertext)
			},
			_parse: function(a, b) {
				return "string" == typeof a ? b.parse(a, this) : a
			}
		}),
		p = (p.kdf = {}).OpenSSL = {
			execute: function(a, b, c, d) {
				d || (d = s.random(8));
				a = w.create({
					keySize: b + c
				}).compute(a, d);
				c = s.create(a.words.slice(b), 4 * c);
				a.sigBytes = 4 * b;
				return n.create({
					key: a,
					iv: c,
					salt: d
				})
			}
		}, c = d.PasswordBasedCipher = a.extend({
			cfg: a.cfg.extend({
				kdf: p
			}),
			encrypt: function(b, c, d, l) {
				l = this.cfg.extend(l);
				d = l.kdf.execute(d,
					b.keySize, b.ivSize);
				l.iv = d.iv;
				b = a.encrypt.call(this, b, c, d.key, l);
				b.mixIn(d);
				return b
			},
			decrypt: function(b, c, d, l) {
				l = this.cfg.extend(l);
				c = this._parse(c, l.format);
				d = l.kdf.execute(d, b.keySize, b.ivSize, c.salt);
				l.iv = d.iv;
				return a.decrypt.call(this, b, c, d.key, l)
			}
		})
}();
(function() {
	for (var u = CryptoJS, p = u.lib.BlockCipher, d = u.algo, l = [], s = [], t = [], r = [], w = [], v = [], b = [], x = [], q = [], n = [], a = [], c = 0; 256 > c; c++) a[c] = 128 > c ? c << 1 : c << 1 ^ 283;
	for (var e = 0, j = 0, c = 0; 256 > c; c++) {
		var k = j ^ j << 1 ^ j << 2 ^ j << 3 ^ j << 4,
			k = k >>> 8 ^ k & 255 ^ 99;
		l[e] = k;
		s[k] = e;
		var z = a[e],
			F = a[z],
			G = a[F],
			y = 257 * a[k] ^ 16843008 * k;
		t[e] = y << 24 | y >>> 8;
		r[e] = y << 16 | y >>> 16;
		w[e] = y << 8 | y >>> 24;
		v[e] = y;
		y = 16843009 * G ^ 65537 * F ^ 257 * z ^ 16843008 * e;
		b[k] = y << 24 | y >>> 8;
		x[k] = y << 16 | y >>> 16;
		q[k] = y << 8 | y >>> 24;
		n[k] = y;
		e ? (e = z ^ a[a[a[G ^ z]]], j ^= a[a[j]]) : e = j = 1
	}
	var H = [0, 1, 2, 4, 8,
		16, 32, 64, 128, 27, 54
	],
		d = d.AES = p.extend({
			_doReset: function() {
				for (var a = this._key, c = a.words, d = a.sigBytes / 4, a = 4 * ((this._nRounds = d + 6) + 1), e = this._keySchedule = [], j = 0; j < a; j++)
					if (j < d) e[j] = c[j];
					else {
						var k = e[j - 1];
						j % d ? 6 < d && 4 == j % d && (k = l[k >>> 24] << 24 | l[k >>> 16 & 255] << 16 | l[k >>> 8 & 255] << 8 | l[k & 255]) : (k = k << 8 | k >>> 24, k = l[k >>> 24] << 24 | l[k >>> 16 & 255] << 16 | l[k >>> 8 & 255] << 8 | l[k & 255], k ^= H[j / d | 0] << 24);
						e[j] = e[j - d] ^ k
					}
				c = this._invKeySchedule = [];
				for (d = 0; d < a; d++) j = a - d, k = d % 4 ? e[j] : e[j - 4], c[d] = 4 > d || 4 >= j ? k : b[l[k >>> 24]] ^ x[l[k >>> 16 & 255]] ^ q[l[k >>>
					8 & 255]] ^ n[l[k & 255]]
			},
			encryptBlock: function(a, b) {
				this._doCryptBlock(a, b, this._keySchedule, t, r, w, v, l)
			},
			decryptBlock: function(a, c) {
				var d = a[c + 1];
				a[c + 1] = a[c + 3];
				a[c + 3] = d;
				this._doCryptBlock(a, c, this._invKeySchedule, b, x, q, n, s);
				d = a[c + 1];
				a[c + 1] = a[c + 3];
				a[c + 3] = d
			},
			_doCryptBlock: function(a, b, c, d, e, j, l, f) {
				for (var m = this._nRounds, g = a[b] ^ c[0], h = a[b + 1] ^ c[1], k = a[b + 2] ^ c[2], n = a[b + 3] ^ c[3], p = 4, r = 1; r < m; r++) var q = d[g >>> 24] ^ e[h >>> 16 & 255] ^ j[k >>> 8 & 255] ^ l[n & 255] ^ c[p++],
				s = d[h >>> 24] ^ e[k >>> 16 & 255] ^ j[n >>> 8 & 255] ^ l[g & 255] ^ c[p++], t =
					d[k >>> 24] ^ e[n >>> 16 & 255] ^ j[g >>> 8 & 255] ^ l[h & 255] ^ c[p++], n = d[n >>> 24] ^ e[g >>> 16 & 255] ^ j[h >>> 8 & 255] ^ l[k & 255] ^ c[p++], g = q, h = s, k = t;
				q = (f[g >>> 24] << 24 | f[h >>> 16 & 255] << 16 | f[k >>> 8 & 255] << 8 | f[n & 255]) ^ c[p++];
				s = (f[h >>> 24] << 24 | f[k >>> 16 & 255] << 16 | f[n >>> 8 & 255] << 8 | f[g & 255]) ^ c[p++];
				t = (f[k >>> 24] << 24 | f[n >>> 16 & 255] << 16 | f[g >>> 8 & 255] << 8 | f[h & 255]) ^ c[p++];
				n = (f[n >>> 24] << 24 | f[g >>> 16 & 255] << 16 | f[h >>> 8 & 255] << 8 | f[k & 255]) ^ c[p++];
				a[b] = q;
				a[b + 1] = s;
				a[b + 2] = t;
				a[b + 3] = n
			},
			keySize: 8
		});
	u.AES = p._createHelper(d)
})();

/* Ported to JavaScript from Java 07/01/14.
 *
 * Ported from C to Java by Dmitry Skiba [sahn0], 23/02/08.
 * Original: http://cds.xs4all.nl:8081/ecdh/
 */
/* Generic 64-bit integer implementation of Curve25519 ECDH
 * Written by Matthijs van Duin, 200608242056
 * Public domain.
 *
 * Based on work by Daniel J Bernstein, http://cr.yp.to/ecdh.html
 */

var curve25519 = function () {

    //region Constants

    var KEY_SIZE = 32;

    /* array length */
    var UNPACKED_SIZE = 16;

    /* group order (a prime near 2^252+2^124) */
    var ORDER = [
        237, 211, 245, 92,
        26, 99, 18, 88,
        214, 156, 247, 162,
        222, 249, 222, 20,
        0, 0, 0, 0,
        0, 0, 0, 0,
        0, 0, 0, 0,
        0, 0, 0, 16
    ];

    /* smallest multiple of the order that's >= 2^255 */
    var ORDER_TIMES_8 = [
        104, 159, 174, 231,
        210, 24, 147, 192,
        178, 230, 188, 23,
        245, 206, 247, 166,
        0, 0, 0, 0,
        0, 0, 0, 0,
        0, 0, 0, 0,
        0, 0, 0, 128
    ];

    /* constants 2Gy and 1/(2Gy) */
    var BASE_2Y = [
        22587, 610, 29883, 44076,
        15515, 9479, 25859, 56197,
        23910, 4462, 17831, 16322,
        62102, 36542, 52412, 16035
    ];

    var BASE_R2Y = [
        5744, 16384, 61977, 54121,
        8776, 18501, 26522, 34893,
        23833, 5823, 55924, 58749,
        24147, 14085, 13606, 6080
    ];

    var C1 = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var C9 = [9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var C486671 = [0x6D0F, 0x0007, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    var C39420360 = [0x81C8, 0x0259, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];

    var P25 = 33554431; /* (1 << 25) - 1 */
    var P26 = 67108863; /* (1 << 26) - 1 */

    //#endregion

    //region Key Agreement

    /* Private key clamping
     *   k [out] your private key for key agreement
     *   k  [in]  32 random bytes
     */
    function clamp (k) {
        k[31] &= 0x7F;
        k[31] |= 0x40;
        k[ 0] &= 0xF8;
    }

    //endregion

    //region radix 2^8 math

    function cpy32 (d, s) {
        for (var i = 0; i < 32; i++)
            d[i] = s[i];
    }

    /* p[m..n+m-1] = q[m..n+m-1] + z * x */
    /* n is the size of x */
    /* n+m is the size of p and q */
    function mula_small (p, q, m, x, n, z) {
        m = m | 0;
        n = n | 0;
        z = z | 0;

        var v = 0;
        for (var i = 0; i < n; ++i) {
            v += (q[i + m] & 0xFF) + z * (x[i] & 0xFF);
            p[i + m] = (v & 0xFF);
            v >>= 8;
        }

        return v;
    }

    /* p += x * y * z  where z is a small integer
     * x is size 32, y is size t, p is size 32+t
     * y is allowed to overlap with p+32 if you don't care about the upper half  */
    function mula32 (p, x, y, t, z) {
        t = t | 0;
        z = z | 0;

        var n = 31;
        var w = 0;
        var i = 0;
        for (; i < t; i++) {
            var zy = z * (y[i] & 0xFF);
            w += mula_small(p, p, i, x, n, zy) + (p[i+n] & 0xFF) + zy * (x[n] & 0xFF);
            p[i + n] = w & 0xFF;
            w >>= 8;
        }
        p[i + n] = (w + (p[i + n] & 0xFF)) & 0xFF;
        return w >> 8;
    }

    /* divide r (size n) by d (size t), returning quotient q and remainder r
     * quotient is size n-t+1, remainder is size t
     * requires t > 0 && d[t-1] !== 0
     * requires that r[-1] and d[-1] are valid memory locations
     * q may overlap with r+t */
    function divmod (q, r, n, d, t) {
        n = n | 0;
        t = t | 0;

        var rn = 0;
        var dt = (d[t - 1] & 0xFF) << 8;
        if (t > 1)
            dt |= (d[t - 2] & 0xFF);

        while (n-- >= t) {
            var z = (rn << 16) | ((r[n] & 0xFF) << 8);
            if (n > 0)
                z |= (r[n - 1] & 0xFF);

            var i = n - t + 1;
            z /= dt;
            rn += mula_small(r, r, i, d, t, -z);
            q[i] = (z + rn) & 0xFF;
            /* rn is 0 or -1 (underflow) */
            mula_small(r, r, i, d, t, -rn);
            rn = r[n] & 0xFF;
            r[n] = 0;
        }

        r[t-1] = rn & 0xFF;
    }

    function numsize (x, n) {
        while (n-- !== 0 && x[n] === 0) { }
        return n + 1;
    }

    /* Returns x if a contains the gcd, y if b.
     * Also, the returned buffer contains the inverse of a mod b,
     * as 32-byte signed.
     * x and y must have 64 bytes space for temporary use.
     * requires that a[-1] and b[-1] are valid memory locations  */
    function egcd32 (x, y, a, b) {
        var an, bn = 32, qn, i;
        for (i = 0; i < 32; i++)
            x[i] = y[i] = 0;
        x[0] = 1;
        an = numsize(a, 32);
        if (an === 0)
            return y; /* division by zero */
        var temp = new Array(32);
        while (true) {
            qn = bn - an + 1;
            divmod(temp, b, bn, a, an);
            bn = numsize(b, bn);
            if (bn === 0)
                return x;
            mula32(y, x, temp, qn, -1);

            qn = an - bn + 1;
            divmod(temp, a, an, b, bn);
            an = numsize(a, an);
            if (an === 0)
                return y;
            mula32(x, y, temp, qn, -1);
        }
    }

    //endregion

    //region radix 2^25.5 GF(2^255-19) math

    //region pack / unpack

    /* Convert to internal format from little-endian byte format */
    function unpack (x, m) {
        for (var i = 0; i < KEY_SIZE; i += 2)
            x[i / 2] = m[i] & 0xFF | ((m[i + 1] & 0xFF) << 8);
    }

    /* Check if reduced-form input >= 2^255-19 */
    function is_overflow (x) {
        return (
            ((x[0] > P26 - 19)) &&
                ((x[1] & x[3] & x[5] & x[7] & x[9]) === P25) &&
                ((x[2] & x[4] & x[6] & x[8]) === P26)
            ) || (x[9] > P25);
    }

    /* Convert from internal format to little-endian byte format.  The
     * number must be in a reduced form which is output by the following ops:
     *     unpack, mul, sqr
     *     set --  if input in range 0 .. P25
     * If you're unsure if the number is reduced, first multiply it by 1.  */
    function pack (x, m) {
        for (var i = 0; i < UNPACKED_SIZE; ++i) {
            m[2 * i] = x[i] & 0x00FF;
            m[2 * i + 1] = (x[i] & 0xFF00) >> 8;
        }
    }

    //endregion

    function createUnpackedArray () {
        return new Uint16Array(UNPACKED_SIZE);
    }

    /* Copy a number */
    function cpy (d, s) {
        for (var i = 0; i < UNPACKED_SIZE; ++i)
            d[i] = s[i];
    }

    /* Set a number to value, which must be in range -185861411 .. 185861411 */
    function set (d, s) {
        d[0] = s;
        for (var i = 1; i < UNPACKED_SIZE; ++i)
            d[i] = 0;
    }

    /* Add/subtract two numbers.  The inputs must be in reduced form, and the
     * output isn't, so to do another addition or subtraction on the output,
     * first multiply it by one to reduce it. */
    var add = c255laddmodp;
    var sub = c255lsubmodp;

    /* Multiply a number by a small integer in range -185861411 .. 185861411.
     * The output is in reduced form, the input x need not be.  x and xy may point
     * to the same buffer. */
    var mul_small = c255lmulasmall;

    /* Multiply two numbers.  The output is in reduced form, the inputs need not be. */
    var mul = c255lmulmodp;

    /* Square a number.  Optimization of  mul25519(x2, x, x)  */
    var sqr = c255lsqrmodp;

    /* Calculates a reciprocal.  The output is in reduced form, the inputs need not
     * be.  Simply calculates  y = x^(p-2)  so it's not too fast. */
    /* When sqrtassist is true, it instead calculates y = x^((p-5)/8) */
    function recip (y, x, sqrtassist) {
        var t0 = createUnpackedArray();
        var t1 = createUnpackedArray();
        var t2 = createUnpackedArray();
        var t3 = createUnpackedArray();
        var t4 = createUnpackedArray();

        /* the chain for x^(2^255-21) is straight from djb's implementation */
        var i;
        sqr(t1, x); /*  2 === 2 * 1	*/
        sqr(t2, t1); /*  4 === 2 * 2	*/
        sqr(t0, t2); /*  8 === 2 * 4	*/
        mul(t2, t0, x); /*  9 === 8 + 1	*/
        mul(t0, t2, t1); /* 11 === 9 + 2	*/
        sqr(t1, t0); /* 22 === 2 * 11	*/
        mul(t3, t1, t2); /* 31 === 22 + 9 === 2^5   - 2^0	*/
        sqr(t1, t3); /* 2^6   - 2^1	*/
        sqr(t2, t1); /* 2^7   - 2^2	*/
        sqr(t1, t2); /* 2^8   - 2^3	*/
        sqr(t2, t1); /* 2^9   - 2^4	*/
        sqr(t1, t2); /* 2^10  - 2^5	*/
        mul(t2, t1, t3); /* 2^10  - 2^0	*/
        sqr(t1, t2); /* 2^11  - 2^1	*/
        sqr(t3, t1); /* 2^12  - 2^2	*/
        for (i = 1; i < 5; i++) {
            sqr(t1, t3);
            sqr(t3, t1);
        } /* t3 */ /* 2^20  - 2^10	*/
        mul(t1, t3, t2); /* 2^20  - 2^0	*/
        sqr(t3, t1); /* 2^21  - 2^1	*/
        sqr(t4, t3); /* 2^22  - 2^2	*/
        for (i = 1; i < 10; i++) {
            sqr(t3, t4);
            sqr(t4, t3);
        } /* t4 */ /* 2^40  - 2^20	*/
        mul(t3, t4, t1); /* 2^40  - 2^0	*/
        for (i = 0; i < 5; i++) {
            sqr(t1, t3);
            sqr(t3, t1);
        } /* t3 */ /* 2^50  - 2^10	*/
        mul(t1, t3, t2); /* 2^50  - 2^0	*/
        sqr(t2, t1); /* 2^51  - 2^1	*/
        sqr(t3, t2); /* 2^52  - 2^2	*/
        for (i = 1; i < 25; i++) {
            sqr(t2, t3);
            sqr(t3, t2);
        } /* t3 */ /* 2^100 - 2^50 */
        mul(t2, t3, t1); /* 2^100 - 2^0	*/
        sqr(t3, t2); /* 2^101 - 2^1	*/
        sqr(t4, t3); /* 2^102 - 2^2	*/
        for (i = 1; i < 50; i++) {
            sqr(t3, t4);
            sqr(t4, t3);
        } /* t4 */ /* 2^200 - 2^100 */
        mul(t3, t4, t2); /* 2^200 - 2^0	*/
        for (i = 0; i < 25; i++) {
            sqr(t4, t3);
            sqr(t3, t4);
        } /* t3 */ /* 2^250 - 2^50	*/
        mul(t2, t3, t1); /* 2^250 - 2^0	*/
        sqr(t1, t2); /* 2^251 - 2^1	*/
        sqr(t2, t1); /* 2^252 - 2^2	*/
        if (sqrtassist !== 0) {
            mul(y, x, t2); /* 2^252 - 3 */
        } else {
            sqr(t1, t2); /* 2^253 - 2^3	*/
            sqr(t2, t1); /* 2^254 - 2^4	*/
            sqr(t1, t2); /* 2^255 - 2^5	*/
            mul(y, t1, t0); /* 2^255 - 21	*/
        }
    }

    /* checks if x is "negative", requires reduced input */
    function is_negative (x) {
        var isOverflowOrNegative = is_overflow(x) || x[9] < 0;
        var leastSignificantBit = x[0] & 1;
        return ((isOverflowOrNegative ? 1 : 0) ^ leastSignificantBit) & 0xFFFFFFFF;
    }

    /* a square root */
    function sqrt (x, u) {
        var v = createUnpackedArray();
        var t1 = createUnpackedArray();
        var t2 = createUnpackedArray();

        add(t1, u, u); /* t1 = 2u		*/
        recip(v, t1, 1); /* v = (2u)^((p-5)/8)	*/
        sqr(x, v); /* x = v^2		*/
        mul(t2, t1, x); /* t2 = 2uv^2		*/
        sub(t2, t2, C1); /* t2 = 2uv^2-1		*/
        mul(t1, v, t2); /* t1 = v(2uv^2-1)	*/
        mul(x, u, t1); /* x = uv(2uv^2-1)	*/
    }

    //endregion

    //region JavaScript Fast Math

    function c255lsqr8h (a7, a6, a5, a4, a3, a2, a1, a0) {
        var r = [];
        var v;
        r[0] = (v = a0*a0) & 0xFFFF;
        r[1] = (v = ((v / 0x10000) | 0) + 2*a0*a1) & 0xFFFF;
        r[2] = (v = ((v / 0x10000) | 0) + 2*a0*a2 + a1*a1) & 0xFFFF;
        r[3] = (v = ((v / 0x10000) | 0) + 2*a0*a3 + 2*a1*a2) & 0xFFFF;
        r[4] = (v = ((v / 0x10000) | 0) + 2*a0*a4 + 2*a1*a3 + a2*a2) & 0xFFFF;
        r[5] = (v = ((v / 0x10000) | 0) + 2*a0*a5 + 2*a1*a4 + 2*a2*a3) & 0xFFFF;
        r[6] = (v = ((v / 0x10000) | 0) + 2*a0*a6 + 2*a1*a5 + 2*a2*a4 + a3*a3) & 0xFFFF;
        r[7] = (v = ((v / 0x10000) | 0) + 2*a0*a7 + 2*a1*a6 + 2*a2*a5 + 2*a3*a4) & 0xFFFF;
        r[8] = (v = ((v / 0x10000) | 0) + 2*a1*a7 + 2*a2*a6 + 2*a3*a5 + a4*a4) & 0xFFFF;
        r[9] = (v = ((v / 0x10000) | 0) + 2*a2*a7 + 2*a3*a6 + 2*a4*a5) & 0xFFFF;
        r[10] = (v = ((v / 0x10000) | 0) + 2*a3*a7 + 2*a4*a6 + a5*a5) & 0xFFFF;
        r[11] = (v = ((v / 0x10000) | 0) + 2*a4*a7 + 2*a5*a6) & 0xFFFF;
        r[12] = (v = ((v / 0x10000) | 0) + 2*a5*a7 + a6*a6) & 0xFFFF;
        r[13] = (v = ((v / 0x10000) | 0) + 2*a6*a7) & 0xFFFF;
        r[14] = (v = ((v / 0x10000) | 0) + a7*a7) & 0xFFFF;
        r[15] = ((v / 0x10000) | 0);
        return r;
    }

    function c255lsqrmodp (r, a) {
        var x = c255lsqr8h(a[15], a[14], a[13], a[12], a[11], a[10], a[9], a[8]);
        var z = c255lsqr8h(a[7], a[6], a[5], a[4], a[3], a[2], a[1], a[0]);
        var y = c255lsqr8h(a[15] + a[7], a[14] + a[6], a[13] + a[5], a[12] + a[4], a[11] + a[3], a[10] + a[2], a[9] + a[1], a[8] + a[0]);

        var v;
        r[0] = (v = 0x800000 + z[0] + (y[8] -x[8] -z[8] + x[0] -0x80) * 38) & 0xFFFF;
        r[1] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[1] + (y[9] -x[9] -z[9] + x[1]) * 38) & 0xFFFF;
        r[2] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[2] + (y[10] -x[10] -z[10] + x[2]) * 38) & 0xFFFF;
        r[3] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[3] + (y[11] -x[11] -z[11] + x[3]) * 38) & 0xFFFF;
        r[4] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[4] + (y[12] -x[12] -z[12] + x[4]) * 38) & 0xFFFF;
        r[5] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[5] + (y[13] -x[13] -z[13] + x[5]) * 38) & 0xFFFF;
        r[6] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[6] + (y[14] -x[14] -z[14] + x[6]) * 38) & 0xFFFF;
        r[7] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[7] + (y[15] -x[15] -z[15] + x[7]) * 38) & 0xFFFF;
        r[8] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[8] + y[0] -x[0] -z[0] + x[8] * 38) & 0xFFFF;
        r[9] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[9] + y[1] -x[1] -z[1] + x[9] * 38) & 0xFFFF;
        r[10] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[10] + y[2] -x[2] -z[2] + x[10] * 38) & 0xFFFF;
        r[11] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[11] + y[3] -x[3] -z[3] + x[11] * 38) & 0xFFFF;
        r[12] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[12] + y[4] -x[4] -z[4] + x[12] * 38) & 0xFFFF;
        r[13] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[13] + y[5] -x[5] -z[5] + x[13] * 38) & 0xFFFF;
        r[14] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[14] + y[6] -x[6] -z[6] + x[14] * 38) & 0xFFFF;
        var r15 = 0x7fff80 + ((v / 0x10000) | 0) + z[15] + y[7] -x[7] -z[7] + x[15] * 38;
        c255lreduce(r, r15);
    }

    function c255lmul8h (a7, a6, a5, a4, a3, a2, a1, a0, b7, b6, b5, b4, b3, b2, b1, b0) {
        var r = [];
        var v;
        r[0] = (v = a0*b0) & 0xFFFF;
        r[1] = (v = ((v / 0x10000) | 0) + a0*b1 + a1*b0) & 0xFFFF;
        r[2] = (v = ((v / 0x10000) | 0) + a0*b2 + a1*b1 + a2*b0) & 0xFFFF;
        r[3] = (v = ((v / 0x10000) | 0) + a0*b3 + a1*b2 + a2*b1 + a3*b0) & 0xFFFF;
        r[4] = (v = ((v / 0x10000) | 0) + a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0) & 0xFFFF;
        r[5] = (v = ((v / 0x10000) | 0) + a0*b5 + a1*b4 + a2*b3 + a3*b2 + a4*b1 + a5*b0) & 0xFFFF;
        r[6] = (v = ((v / 0x10000) | 0) + a0*b6 + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1 + a6*b0) & 0xFFFF;
        r[7] = (v = ((v / 0x10000) | 0) + a0*b7 + a1*b6 + a2*b5 + a3*b4 + a4*b3 + a5*b2 + a6*b1 + a7*b0) & 0xFFFF;
        r[8] = (v = ((v / 0x10000) | 0) + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1) & 0xFFFF;
        r[9] = (v = ((v / 0x10000) | 0) + a2*b7 + a3*b6 + a4*b5 + a5*b4 + a6*b3 + a7*b2) & 0xFFFF;
        r[10] = (v = ((v / 0x10000) | 0) + a3*b7 + a4*b6 + a5*b5 + a6*b4 + a7*b3) & 0xFFFF;
        r[11] = (v = ((v / 0x10000) | 0) + a4*b7 + a5*b6 + a6*b5 + a7*b4) & 0xFFFF;
        r[12] = (v = ((v / 0x10000) | 0) + a5*b7 + a6*b6 + a7*b5) & 0xFFFF;
        r[13] = (v = ((v / 0x10000) | 0) + a6*b7 + a7*b6) & 0xFFFF;
        r[14] = (v = ((v / 0x10000) | 0) + a7*b7) & 0xFFFF;
        r[15] = ((v / 0x10000) | 0);
        return r;
    }

    function c255lmulmodp (r, a, b) {
        // Karatsuba multiplication scheme: x*y = (b^2+b)*x1*y1 - b*(x1-x0)*(y1-y0) + (b+1)*x0*y0
        var x = c255lmul8h(a[15], a[14], a[13], a[12], a[11], a[10], a[9], a[8], b[15], b[14], b[13], b[12], b[11], b[10], b[9], b[8]);
        var z = c255lmul8h(a[7], a[6], a[5], a[4], a[3], a[2], a[1], a[0], b[7], b[6], b[5], b[4], b[3], b[2], b[1], b[0]);
        var y = c255lmul8h(a[15] + a[7], a[14] + a[6], a[13] + a[5], a[12] + a[4], a[11] + a[3], a[10] + a[2], a[9] + a[1], a[8] + a[0],
            b[15] + b[7], b[14] + b[6], b[13] + b[5], b[12] + b[4], b[11] + b[3], b[10] + b[2], b[9] + b[1], b[8] + b[0]);

        var v;
        r[0] = (v = 0x800000 + z[0] + (y[8] -x[8] -z[8] + x[0] -0x80) * 38) & 0xFFFF;
        r[1] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[1] + (y[9] -x[9] -z[9] + x[1]) * 38) & 0xFFFF;
        r[2] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[2] + (y[10] -x[10] -z[10] + x[2]) * 38) & 0xFFFF;
        r[3] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[3] + (y[11] -x[11] -z[11] + x[3]) * 38) & 0xFFFF;
        r[4] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[4] + (y[12] -x[12] -z[12] + x[4]) * 38) & 0xFFFF;
        r[5] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[5] + (y[13] -x[13] -z[13] + x[5]) * 38) & 0xFFFF;
        r[6] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[6] + (y[14] -x[14] -z[14] + x[6]) * 38) & 0xFFFF;
        r[7] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[7] + (y[15] -x[15] -z[15] + x[7]) * 38) & 0xFFFF;
        r[8] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[8] + y[0] -x[0] -z[0] + x[8] * 38) & 0xFFFF;
        r[9] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[9] + y[1] -x[1] -z[1] + x[9] * 38) & 0xFFFF;
        r[10] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[10] + y[2] -x[2] -z[2] + x[10] * 38) & 0xFFFF;
        r[11] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[11] + y[3] -x[3] -z[3] + x[11] * 38) & 0xFFFF;
        r[12] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[12] + y[4] -x[4] -z[4] + x[12] * 38) & 0xFFFF;
        r[13] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[13] + y[5] -x[5] -z[5] + x[13] * 38) & 0xFFFF;
        r[14] = (v = 0x7fff80 + ((v / 0x10000) | 0) + z[14] + y[6] -x[6] -z[6] + x[14] * 38) & 0xFFFF;
        var r15 = 0x7fff80 + ((v / 0x10000) | 0) + z[15] + y[7] -x[7] -z[7] + x[15] * 38;
        c255lreduce(r, r15);
    }

    function c255lreduce (a, a15) {
        var v = a15;
        a[15] = v & 0x7FFF;
        v = ((v / 0x8000) | 0) * 19;
        for (var i = 0; i <= 14; ++i) {
            a[i] = (v += a[i]) & 0xFFFF;
            v = ((v / 0x10000) | 0);
        }

        a[15] += v;
    }

    function c255laddmodp (r, a, b) {
        var v;
        r[0] = (v = (((a[15] / 0x8000) | 0) + ((b[15] / 0x8000) | 0)) * 19 + a[0] + b[0]) & 0xFFFF;
        for (var i = 1; i <= 14; ++i)
            r[i] = (v = ((v / 0x10000) | 0) + a[i] + b[i]) & 0xFFFF;

        r[15] = ((v / 0x10000) | 0) + (a[15] & 0x7FFF) + (b[15] & 0x7FFF);
    }

    function c255lsubmodp (r, a, b) {
        var v;
        r[0] = (v = 0x80000 + (((a[15] / 0x8000) | 0) - ((b[15] / 0x8000) | 0) - 1) * 19 + a[0] - b[0]) & 0xFFFF;
        for (var i = 1; i <= 14; ++i)
            r[i] = (v = ((v / 0x10000) | 0) + 0x7fff8 + a[i] - b[i]) & 0xFFFF;

        r[15] = ((v / 0x10000) | 0) + 0x7ff8 + (a[15] & 0x7FFF) - (b[15] & 0x7FFF);
    }

    function c255lmulasmall (r, a, m) {
        var v;
        r[0] = (v = a[0] * m) & 0xFFFF;
        for (var i = 1; i <= 14; ++i)
            r[i] = (v = ((v / 0x10000) | 0) + a[i]*m) & 0xFFFF;

        var r15 = ((v / 0x10000) | 0) + a[15]*m;
        c255lreduce(r, r15);
    }

    //endregion

    /********************* Elliptic curve *********************/

    /* y^2 = x^3 + 486662 x^2 + x  over GF(2^255-19) */

    /* t1 = ax + az
     * t2 = ax - az  */
    function mont_prep (t1, t2, ax, az) {
        add(t1, ax, az);
        sub(t2, ax, az);
    }

    /* A = P + Q   where
     *  X(A) = ax/az
     *  X(P) = (t1+t2)/(t1-t2)
     *  X(Q) = (t3+t4)/(t3-t4)
     *  X(P-Q) = dx
     * clobbers t1 and t2, preserves t3 and t4  */
    function mont_add (t1, t2, t3, t4, ax, az, dx) {
        mul(ax, t2, t3);
        mul(az, t1, t4);
        add(t1, ax, az);
        sub(t2, ax, az);
        sqr(ax, t1);
        sqr(t1, t2);
        mul(az, t1, dx);
    }

    /* B = 2 * Q   where
     *  X(B) = bx/bz
     *  X(Q) = (t3+t4)/(t3-t4)
     * clobbers t1 and t2, preserves t3 and t4  */
    function mont_dbl (t1, t2, t3, t4, bx, bz) {
        sqr(t1, t3);
        sqr(t2, t4);
        mul(bx, t1, t2);
        sub(t2, t1, t2);
        mul_small(bz, t2, 121665);
        add(t1, t1, bz);
        mul(bz, t1, t2);
    }

    /* Y^2 = X^3 + 486662 X^2 + X
     * t is a temporary  */
    function x_to_y2 (t, y2, x) {
        sqr(t, x);
        mul_small(y2, x, 486662);
        add(t, t, y2);
        add(t, t, C1);
        mul(y2, t, x);
    }

    /* P = kG   and  s = sign(P)/k  */
    function core (Px, s, k, Gx) {
        var dx = createUnpackedArray();
        var t1 = createUnpackedArray();
        var t2 = createUnpackedArray();
        var t3 = createUnpackedArray();
        var t4 = createUnpackedArray();
        var x = [createUnpackedArray(), createUnpackedArray()];
        var z = [createUnpackedArray(), createUnpackedArray()];
        var i, j;

        /* unpack the base */
        if (Gx !== null)
            unpack(dx, Gx);
        else
            set(dx, 9);

        /* 0G = point-at-infinity */
        set(x[0], 1);
        set(z[0], 0);

        /* 1G = G */
        cpy(x[1], dx);
        set(z[1], 1);

        for (i = 32; i-- !== 0;) {
            for (j = 8; j-- !== 0;) {
                /* swap arguments depending on bit */
                var bit1 = (k[i] & 0xFF) >> j & 1;
                var bit0 = ~(k[i] & 0xFF) >> j & 1;
                var ax = x[bit0];
                var az = z[bit0];
                var bx = x[bit1];
                var bz = z[bit1];

                /* a' = a + b	*/
                /* b' = 2 b	*/
                mont_prep(t1, t2, ax, az);
                mont_prep(t3, t4, bx, bz);
                mont_add(t1, t2, t3, t4, ax, az, dx);
                mont_dbl(t1, t2, t3, t4, bx, bz);
            }
        }

        recip(t1, z[0], 0);
        mul(dx, x[0], t1);

        pack(dx, Px);

        /* calculate s such that s abs(P) = G  .. assumes G is std base point */
        if (s !== null) {
            x_to_y2(t2, t1, dx); /* t1 = Py^2  */
            recip(t3, z[1], 0); /* where Q=P+G ... */
            mul(t2, x[1], t3); /* t2 = Qx  */
            add(t2, t2, dx); /* t2 = Qx + Px  */
            add(t2, t2, C486671); /* t2 = Qx + Px + Gx + 486662  */
            sub(dx, dx, C9); /* dx = Px - Gx  */
            sqr(t3, dx); /* t3 = (Px - Gx)^2  */
            mul(dx, t2, t3); /* dx = t2 (Px - Gx)^2  */
            sub(dx, dx, t1); /* dx = t2 (Px - Gx)^2 - Py^2  */
            sub(dx, dx, C39420360); /* dx = t2 (Px - Gx)^2 - Py^2 - Gy^2  */
            mul(t1, dx, BASE_R2Y); /* t1 = -Py  */

            if (is_negative(t1) !== 0)    /* sign is 1, so just copy  */
                cpy32(s, k);
            else            /* sign is -1, so negate  */
                mula_small(s, ORDER_TIMES_8, 0, k, 32, -1);

            /* reduce s mod q
             * (is this needed?  do it just in case, it's fast anyway) */
            //divmod((dstptr) t1, s, 32, order25519, 32);

            /* take reciprocal of s mod q */
            var temp1 = new Array(32);
            var temp2 = new Array(64);
            var temp3 = new Array(64);
            cpy32(temp1, ORDER);
            cpy32(s, egcd32(temp2, temp3, s, temp1));
            if ((s[31] & 0x80) !== 0)
                mula_small(s, s, 0, ORDER, 32, 1);

        }
    }

    /********* DIGITAL SIGNATURES *********/

    /* deterministic EC-KCDSA
     *
     *    s is the private key for signing
     *    P is the corresponding public key
     *    Z is the context data (signer public key or certificate, etc)
     *
     * signing:
     *
     *    m = hash(Z, message)
     *    x = hash(m, s)
     *    keygen25519(Y, NULL, x);
     *    r = hash(Y);
     *    h = m XOR r
     *    sign25519(v, h, x, s);
     *
     *    output (v,r) as the signature
     *
     * verification:
     *
     *    m = hash(Z, message);
     *    h = m XOR r
     *    verify25519(Y, v, h, P)
     *
     *    confirm  r === hash(Y)
     *
     * It would seem to me that it would be simpler to have the signer directly do
     * h = hash(m, Y) and send that to the recipient instead of r, who can verify
     * the signature by checking h === hash(m, Y).  If there are any problems with
     * such a scheme, please let me know.
     *
     * Also, EC-KCDSA (like most DS algorithms) picks x random, which is a waste of
     * perfectly good entropy, but does allow Y to be calculated in advance of (or
     * parallel to) hashing the message.
     */

    /* Signature generation primitive, calculates (x-h)s mod q
     *   h  [in]  signature hash (of message, signature pub key, and context data)
     *   x  [in]  signature private key
     *   s  [in]  private key for signing
     * returns signature value on success, undefined on failure (use different x or h)
     */

    function sign (h, x, s) {
        // v = (x - h) s  mod q
        var w, i;
        var h1 = new Array(32)
        var x1 = new Array(32);
        var tmp1 = new Array(64);
        var tmp2 = new Array(64);

        // Don't clobber the arguments, be nice!
        cpy32(h1, h);
        cpy32(x1, x);

        // Reduce modulo group order
        var tmp3 = new Array(32);
        divmod(tmp3, h1, 32, ORDER, 32);
        divmod(tmp3, x1, 32, ORDER, 32);

        // v = x1 - h1
        // If v is negative, add the group order to it to become positive.
        // If v was already positive we don't have to worry about overflow
        // when adding the order because v < ORDER and 2*ORDER < 2^256
        var v = new Array(32);
        mula_small(v, x1, 0, h1, 32, -1);
        mula_small(v, v , 0, ORDER, 32, 1);

        // tmp1 = (x-h)*s mod q
        mula32(tmp1, v, s, 32, 1);
        divmod(tmp2, tmp1, 64, ORDER, 32);

        for (w = 0, i = 0; i < 32; i++)
            w |= v[i] = tmp1[i];

        return w !== 0 ? v : undefined;
    }

    /* Signature verification primitive, calculates Y = vP + hG
     *   v  [in]  signature value
     *   h  [in]  signature hash
     *   P  [in]  public key
     *   Returns signature public key
     */
    function verify (v, h, P) {
        /* Y = v abs(P) + h G  */
        var d = new Array(32);
        var p = [createUnpackedArray(), createUnpackedArray()];
        var s = [createUnpackedArray(), createUnpackedArray()];
        var yx = [createUnpackedArray(), createUnpackedArray(), createUnpackedArray()];
        var yz = [createUnpackedArray(), createUnpackedArray(), createUnpackedArray()];
        var t1 = [createUnpackedArray(), createUnpackedArray(), createUnpackedArray()];
        var t2 = [createUnpackedArray(), createUnpackedArray(), createUnpackedArray()];

        var vi = 0, hi = 0, di = 0, nvh = 0, i, j, k;

        /* set p[0] to G and p[1] to P  */

        set(p[0], 9);
        unpack(p[1], P);

        /* set s[0] to P+G and s[1] to P-G  */

        /* s[0] = (Py^2 + Gy^2 - 2 Py Gy)/(Px - Gx)^2 - Px - Gx - 486662  */
        /* s[1] = (Py^2 + Gy^2 + 2 Py Gy)/(Px - Gx)^2 - Px - Gx - 486662  */

        x_to_y2(t1[0], t2[0], p[1]); /* t2[0] = Py^2  */
        sqrt(t1[0], t2[0]); /* t1[0] = Py or -Py  */
        j = is_negative(t1[0]); /*      ... check which  */
        add(t2[0], t2[0], C39420360); /* t2[0] = Py^2 + Gy^2  */
        mul(t2[1], BASE_2Y, t1[0]); /* t2[1] = 2 Py Gy or -2 Py Gy  */
        sub(t1[j], t2[0], t2[1]); /* t1[0] = Py^2 + Gy^2 - 2 Py Gy  */
        add(t1[1 - j], t2[0], t2[1]); /* t1[1] = Py^2 + Gy^2 + 2 Py Gy  */
        cpy(t2[0], p[1]); /* t2[0] = Px  */
        sub(t2[0], t2[0], C9); /* t2[0] = Px - Gx  */
        sqr(t2[1], t2[0]); /* t2[1] = (Px - Gx)^2  */
        recip(t2[0], t2[1], 0); /* t2[0] = 1/(Px - Gx)^2  */
        mul(s[0], t1[0], t2[0]); /* s[0] = t1[0]/(Px - Gx)^2  */
        sub(s[0], s[0], p[1]); /* s[0] = t1[0]/(Px - Gx)^2 - Px  */
        sub(s[0], s[0], C486671); /* s[0] = X(P+G)  */
        mul(s[1], t1[1], t2[0]); /* s[1] = t1[1]/(Px - Gx)^2  */
        sub(s[1], s[1], p[1]); /* s[1] = t1[1]/(Px - Gx)^2 - Px  */
        sub(s[1], s[1], C486671); /* s[1] = X(P-G)  */
        mul_small(s[0], s[0], 1); /* reduce s[0] */
        mul_small(s[1], s[1], 1); /* reduce s[1] */

        /* prepare the chain  */
        for (i = 0; i < 32; i++) {
            vi = (vi >> 8) ^ (v[i] & 0xFF) ^ ((v[i] & 0xFF) << 1);
            hi = (hi >> 8) ^ (h[i] & 0xFF) ^ ((h[i] & 0xFF) << 1);
            nvh = ~(vi ^ hi);
            di = (nvh & (di & 0x80) >> 7) ^ vi;
            di ^= nvh & (di & 0x01) << 1;
            di ^= nvh & (di & 0x02) << 1;
            di ^= nvh & (di & 0x04) << 1;
            di ^= nvh & (di & 0x08) << 1;
            di ^= nvh & (di & 0x10) << 1;
            di ^= nvh & (di & 0x20) << 1;
            di ^= nvh & (di & 0x40) << 1;
            d[i] = di & 0xFF;
        }

        di = ((nvh & (di & 0x80) << 1) ^ vi) >> 8;

        /* initialize state */
        set(yx[0], 1);
        cpy(yx[1], p[di]);
        cpy(yx[2], s[0]);
        set(yz[0], 0);
        set(yz[1], 1);
        set(yz[2], 1);

        /* y[0] is (even)P + (even)G
         * y[1] is (even)P + (odd)G  if current d-bit is 0
         * y[1] is (odd)P + (even)G  if current d-bit is 1
         * y[2] is (odd)P + (odd)G
         */

        vi = 0;
        hi = 0;

        /* and go for it! */
        for (i = 32; i-- !== 0;) {
            vi = (vi << 8) | (v[i] & 0xFF);
            hi = (hi << 8) | (h[i] & 0xFF);
            di = (di << 8) | (d[i] & 0xFF);

            for (j = 8; j-- !== 0;) {
                mont_prep(t1[0], t2[0], yx[0], yz[0]);
                mont_prep(t1[1], t2[1], yx[1], yz[1]);
                mont_prep(t1[2], t2[2], yx[2], yz[2]);

                k = ((vi ^ vi >> 1) >> j & 1)
                    + ((hi ^ hi >> 1) >> j & 1);
                mont_dbl(yx[2], yz[2], t1[k], t2[k], yx[0], yz[0]);

                k = (di >> j & 2) ^ ((di >> j & 1) << 1);
                mont_add(t1[1], t2[1], t1[k], t2[k], yx[1], yz[1],
                    p[di >> j & 1]);

                mont_add(t1[2], t2[2], t1[0], t2[0], yx[2], yz[2],
                    s[((vi ^ hi) >> j & 2) >> 1]);
            }
        }

        k = (vi & 1) + (hi & 1);
        recip(t1[0], yz[k], 0);
        mul(t1[1], yx[k], t1[0]);

        var Y = [];
        pack(t1[1], Y);
        return Y;
    }

    /* Key-pair generation
     *   P  [out] your public key
     *   s  [out] your private key for signing
     *   k  [out] your private key for key agreement
     *   k  [in]  32 random bytes
     * s may be NULL if you don't care
     *
     * WARNING: if s is not NULL, this function has data-dependent timing */
    function keygen (k) {
        var P = [];
        var s = [];
        k = k || [];
        clamp(k);
        core(P, s, k, null);

        return { p: P, s: s, k: k };
    }

    return {
        sign: sign,
        verify: verify,
        keygen: keygen
    };
}();

/*
    NXT address class, extended version (with error guessing).

    Version: 1.0, license: Public Domain, coder: NxtChg (admin@nxtchg.com).
*/

function NxtAddress() {
	var codeword = [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
	var syndrome = [0, 0, 0, 0, 0];

	var gexp = [1, 2, 4, 8, 16, 5, 10, 20, 13, 26, 17, 7, 14, 28, 29, 31, 27, 19, 3, 6, 12, 24, 21, 15, 30, 25, 23, 11, 22, 9, 18, 1];
	var glog = [0, 0, 1, 18, 2, 5, 19, 11, 3, 29, 6, 27, 20, 8, 12, 23, 4, 10, 30, 17, 7, 22, 28, 26, 21, 25, 9, 16, 13, 14, 24, 15];

	var cwmap = [3, 2, 1, 0, 7, 6, 5, 4, 13, 14, 15, 16, 12, 8, 9, 10, 11];

	var alphabet = '23456789ABCDEFGHJKLMNPQRSTUVWXYZ';
	//var alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ345679';

	this.guess = [];

	function ginv(a) {
		return gexp[31 - glog[a]];
	}

	function gmult(a, b) {
		if (a == 0 || b == 0) return 0;

		var idx = (glog[a] + glog[b]) % 31;

		return gexp[idx];
	} //__________________________

	function calc_discrepancy(lambda, r) {
		var discr = 0;

		for (var i = 0; i < r; i++) {
			discr ^= gmult(lambda[i], syndrome[r - i]);
		}

		return discr;
	} //__________________________

	function find_errors(lambda) {
		var errloc = [];

		for (var i = 1; i <= 31; i++) {
			var sum = 0;

			for (var j = 0; j < 5; j++) {
				sum ^= gmult(gexp[(j * i) % 31], lambda[j]);
			}

			if (sum == 0) {
				var pos = 31 - i;
				if (pos > 12 && pos < 27) return [];

				errloc[errloc.length] = pos;
			}
		}

		return errloc;
	} //__________________________

	function guess_errors() {
		var el = 0,
			b = [0, 0, 0, 0, 0],
			t = [];

		var deg_lambda = 0,
			lambda = [1, 0, 0, 0, 0]; // error+erasure locator poly

		// Berlekamp-Massey algorithm to determine error+erasure locator polynomial

		for (var r = 0; r < 4; r++) {
			var discr = calc_discrepancy(lambda, r + 1); // Compute discrepancy at the r-th step in poly-form

			if (discr != 0) {
				deg_lambda = 0;

				for (var i = 0; i < 5; i++) {
					t[i] = lambda[i] ^ gmult(discr, b[i]);

					if (t[i]) deg_lambda = i;
				}

				if (2 * el <= r) {
					el = r + 1 - el;

					for (i = 0; i < 5; i++) {
						b[i] = gmult(lambda[i], ginv(discr));
					}
				}

				lambda = t.slice(); // copy
			}

			b.unshift(0); // shift => mul by x
		}

		// Find roots of the locator polynomial.

		var errloc = find_errors(lambda);

		var errors = errloc.length;

		if (errors < 1 || errors > 2) return false;

		if (deg_lambda != errors) return false; // deg(lambda) unequal to number of roots => uncorrectable error

		// Compute err+eras evaluator poly omega(x) = s(x)*lambda(x) (modulo x**(4)). Also find deg(omega).

		var omega = [0, 0, 0, 0, 0];

		for (var i = 0; i < 4; i++) {
			var t = 0;

			for (var j = 0; j < i; j++) {
				t ^= gmult(syndrome[i + 1 - j], lambda[j]);
			}

			omega[i] = t;
		}

		// Compute error values in poly-form.

		for (r = 0; r < errors; r++) {
			var t = 0;
			var pos = errloc[r];
			var root = 31 - pos;

			for (i = 0; i < 4; i++) // evaluate Omega at alpha^(-i)
			{
				t ^= gmult(omega[i], gexp[(root * i) % 31]);
			}

			if (t) // evaluate Lambda' (derivative) at alpha^(-i); all odd powers disappear
			{
				var denom = gmult(lambda[1], 1) ^ gmult(lambda[3], gexp[(root * 2) % 31]);

				if (denom == 0) return false;

				if (pos > 12) pos -= 14;

				codeword[pos] ^= gmult(t, ginv(denom));
			}
		}

		return true;
	} //__________________________

	function encode() {
		var p = [0, 0, 0, 0];

		for (var i = 12; i >= 0; i--) {
			var fb = codeword[i] ^ p[3];

			p[3] = p[2] ^ gmult(30, fb);
			p[2] = p[1] ^ gmult(6, fb);
			p[1] = p[0] ^ gmult(9, fb);
			p[0] = gmult(17, fb);
		}

		codeword[13] = p[0];
		codeword[14] = p[1];
		codeword[15] = p[2];
		codeword[16] = p[3];
	} //__________________________

	function reset() {
		for (var i = 0; i < 17; i++) codeword[i] = 1;
	} //__________________________

	function set_codeword(cw, len, skip) {
		if (typeof len === 'undefined') len = 17;
		if (typeof skip === 'undefined') skip = -1;

		for (var i = 0, j = 0; i < len; i++) {
			if (i != skip) codeword[cwmap[j++]] = cw[i];
		}
	} //__________________________

	this.add_guess = function() {
		var s = this.toString(),
			len = this.guess.length;

		if (len > 2) return;

		for (var i = 0; i < len; i++) {
			if (this.guess[i] == s) return;
		}

		this.guess[len] = s;
	} //__________________________

	this.ok = function() {
		var sum = 0;

		for (var i = 1; i < 5; i++) {
			for (var j = 0, t = 0; j < 31; j++) {
				if (j > 12 && j < 27) continue;

				var pos = j;
				if (j > 26) pos -= 14;

				t ^= gmult(codeword[pos], gexp[(i * j) % 31]);
			}

			sum |= t;
			syndrome[i] = t;
		}

		return (sum == 0);
	} //__________________________

	function from_acc(acc) {
		var inp = [],
			out = [],
			pos = 0,
			len = acc.length;

		if (len == 20 && acc.charAt(0) != '1') return false;

		for (var i = 0; i < len; i++) {
			inp[i] = acc.charCodeAt(i) - '0'.charCodeAt(0);
		}

		do // base 10 to base 32 conversion
		{
			var divide = 0,
				newlen = 0;

			for (i = 0; i < len; i++) {
				divide = divide * 10 + inp[i];

				if (divide >= 32) {
					inp[newlen++] = divide >> 5;
					divide &= 31;
				} else if (newlen > 0) {
					inp[newlen++] = 0;
				}
			}

			len = newlen;
			out[pos++] = divide;
		}
		while (newlen);

		for (i = 0; i < 13; i++) // copy to codeword in reverse, pad with 0's
		{
			codeword[i] = (--pos >= 0 ? out[i] : 0);
		}

		encode();

		return true;
	} //__________________________

	this.toString = function() {
		var out = 'NXT-';

		for (var i = 0; i < 17; i++) {
			out += alphabet[codeword[cwmap[i]]];

			if ((i & 3) == 3 && i < 13) out += '-';
		}

		return out;
	} //__________________________

	this.account_id = function() {
		var out = '',
			inp = [],
			len = 13;

		for (var i = 0; i < 13; i++) {
			inp[i] = codeword[12 - i];
		}

		do // base 32 to base 10 conversion
		{
			var divide = 0,
				newlen = 0;

			for (i = 0; i < len; i++) {
				divide = divide * 32 + inp[i];

				if (divide >= 10) {
					inp[newlen++] = Math.floor(divide / 10);
					divide %= 10;
				} else if (newlen > 0) {
					inp[newlen++] = 0;
				}
			}

			len = newlen;
			out += String.fromCharCode(divide + '0'.charCodeAt(0));
		}
		while (newlen);

		return out.split("").reverse().join("");
	} //__________________________

	this.set = function(adr, allow_accounts) {
		if (typeof allow_accounts === 'undefined') allow_accounts = true;

		var len = 0;
		this.guess = [];
		reset();

		adr = String(adr);

		adr = adr.replace(/(^\s+)|(\s+$)/g, '').toUpperCase();

		if (adr.indexOf('NXT-') == 0) adr = adr.substr(4);

		if (adr.match(/^\d{1,20}$/g)) // account id
		{
			if (allow_accounts) return from_acc(adr);
		} else // address
		{
			var clean = [];

			for (var i = 0; i < adr.length; i++) {
				var pos = alphabet.indexOf(adr[i]);

				if (pos >= 0) {
					clean[len++] = pos;
					if (len > 18) return false;
				}
			}
		}

		if (len == 16) // guess deletion
		{
			for (var i = 16; i >= 0; i--) {
				for (var j = 0; j < 32; j++) {
					clean[i] = j;

					set_codeword(clean);

					if (this.ok()) this.add_guess();
				}

				if (i > 0) {
					var t = clean[i - 1];
					clean[i - 1] = clean[i];
					clean[i] = t;
				}
			}
		}

		if (len == 18) // guess insertion
		{
			for (var i = 0; i < 18; i++) {
				set_codeword(clean, 18, i);

				if (this.ok()) this.add_guess();
			}
		}

		if (len == 17) {
			set_codeword(clean);

			if (this.ok()) return true;

			if (guess_errors() && this.ok()) this.add_guess();
		}

		reset();

		return false;
	}

	this.format_guess = function(s, org) {
		var d = '',
			list = [];

		s = s.toUpperCase();
		org = org.toUpperCase();

		for (var i = 0; i < s.length;) {
			var m = 0;

			for (var j = 1; j < s.length; j++) {
				var pos = org.indexOf(s.substr(i, j));

				if (pos != -1) {
					if (Math.abs(pos - i) < 3) m = j;
				} else break;
			}

			if (m) {
				list[list.length] = {
					's': i,
					'e': i + m
				};
				i += m;
			} else i++;
		}

		if (list.length == 0) return s;

		for (var i = 0, j = 0; i < s.length; i++) {
			if (i >= list[j].e) {
				var start;

				while (j < list.length - 1) {
					start = list[j++].s;

					if (i < list[j].e || list[j].s >= start) break;
				}
			}

			if (i >= list[j].s && i < list[j].e) {
				d += s.charAt(i);
			} else {
				d += '<b style="color:red">' + s.charAt(i) + '</b>';
			}
		}

		return d;
	}
}
var converters = function() {
	var charToNibble = {};
	var nibbleToChar = [];
	var i;
	for (i = 0; i <= 9; ++i) {
		var character = i.toString();
		charToNibble[character] = i;
		nibbleToChar.push(character);
	}

	for (i = 10; i <= 15; ++i) {
		var lowerChar = String.fromCharCode('a'.charCodeAt(0) + i - 10);
		var upperChar = String.fromCharCode('A'.charCodeAt(0) + i - 10);

		charToNibble[lowerChar] = i;
		charToNibble[upperChar] = i;
		nibbleToChar.push(lowerChar);
	}

	return {
		byteArrayToHexString: function(bytes) {
			var str = '';
			for (var i = 0; i < bytes.length; ++i) {
				if (bytes[i] < 0) {
					bytes[i] += 256;
				}
				str += nibbleToChar[bytes[i] >> 4] + nibbleToChar[bytes[i] & 0x0F];
			}

			return str;
		},
		stringToByteArray: function(str) {
			str = unescape(encodeURIComponent(str)); //temporary

			var bytes = new Array(str.length);
			for (var i = 0; i < str.length; ++i)
				bytes[i] = str.charCodeAt(i);

			return bytes;
		},
		hexStringToByteArray: function(str) {
			var bytes = [];
			var i = 0;
			if (0 !== str.length % 2) {
				bytes.push(charToNibble[str.charAt(0)]);
				++i;
			}

			for (; i < str.length - 1; i += 2)
				bytes.push((charToNibble[str.charAt(i)] << 4) + charToNibble[str.charAt(i + 1)]);

			return bytes;
		},
		stringToHexString: function(str) {
			return this.byteArrayToHexString(this.stringToByteArray(str));
		},
		hexStringToString: function(hex) {
			return this.byteArrayToString(this.hexStringToByteArray(hex));
		},
		checkBytesToIntInput: function(bytes, numBytes, opt_startIndex) {
			var startIndex = opt_startIndex || 0;
			if (startIndex < 0) {
				throw new Error('Start index should not be negative');
			}

			if (bytes.length < startIndex + numBytes) {
				throw new Error('Need at least ' + (numBytes) + ' bytes to convert to an integer');
			}
			return startIndex;
		},
		byteArrayToSignedShort: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 2, opt_startIndex);
			var value = bytes[index];
			value += bytes[index + 1] << 8;
			return value;
		},
		byteArrayToSignedInt32: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 4, opt_startIndex);
			value = bytes[index];
			value += bytes[index + 1] << 8;
			value += bytes[index + 2] << 16;
			value += bytes[index + 3] << 24;
			return value;
		},
		byteArrayToBigInteger: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 8, opt_startIndex);

			var value = new BigInteger("0", 10);

			var temp1, temp2;

			for (var i = 7; i >= 0; i--) {
				temp1 = value.multiply(new BigInteger("256", 10));
				temp2 = temp1.add(new BigInteger(bytes[opt_startIndex + i].toString(10), 10));
				value = temp2;
			}

			return value;
		},
		// create a wordArray that is Big-Endian
		byteArrayToWordArray: function(byteArray) {
			var i = 0,
				offset = 0,
				word = 0,
				len = byteArray.length;
			var words = new Uint32Array(((len / 4) | 0) + (len % 4 == 0 ? 0 : 1));

			while (i < (len - (len % 4))) {
				words[offset++] = (byteArray[i++] << 24) | (byteArray[i++] << 16) | (byteArray[i++] << 8) | (byteArray[i++]);
			}
			if (len % 4 != 0) {
				word = byteArray[i++] << 24;
				if (len % 4 > 1) {
					word = word | byteArray[i++] << 16;
				}
				if (len % 4 > 2) {
					word = word | byteArray[i++] << 8;
				}
				words[offset] = word;
			}
			var wordArray = new Object();
			wordArray.sigBytes = len;
			wordArray.words = words;

			return wordArray;
		},
		// assumes wordArray is Big-Endian
		wordArrayToByteArray: function(wordArray) {
			var len = wordArray.words.length;
			if (len == 0) {
				return new Array(0);
			}
			var byteArray = new Array(wordArray.sigBytes);
			var offset = 0,
				word, i;
			for (i = 0; i < len - 1; i++) {
				word = wordArray.words[i];
				byteArray[offset++] = word >> 24;
				byteArray[offset++] = (word >> 16) & 0xff;
				byteArray[offset++] = (word >> 8) & 0xff;
				byteArray[offset++] = word & 0xff;
			}
			word = wordArray.words[len - 1];
			byteArray[offset++] = word >> 24;
			if (wordArray.sigBytes % 4 == 0) {
				byteArray[offset++] = (word >> 16) & 0xff;
				byteArray[offset++] = (word >> 8) & 0xff;
				byteArray[offset++] = word & 0xff;
			}
			if (wordArray.sigBytes % 4 > 1) {
				byteArray[offset++] = (word >> 16) & 0xff;
			}
			if (wordArray.sigBytes % 4 > 2) {
				byteArray[offset++] = (word >> 8) & 0xff;
			}
			return byteArray;
		},
		byteArrayToString: function(bytes, opt_startIndex, length) {
			if (length == 0) {
				return "";
			}

			if (opt_startIndex && length) {
				var index = this.checkBytesToIntInput(bytes, parseInt(length, 10), parseInt(opt_startIndex, 10));

				bytes = bytes.slice(opt_startIndex, opt_startIndex + length);
			}

			return decodeURIComponent(escape(String.fromCharCode.apply(null, bytes)));
		},
		byteArrayToShortArray: function(byteArray) {
			var shortArray = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
			var i;
			for (i = 0; i < 16; i++) {
				shortArray[i] = byteArray[i * 2] | byteArray[i * 2 + 1] << 8;
			}
			return shortArray;
		},
		shortArrayToByteArray: function(shortArray) {
			var byteArray = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
			var i;
			for (i = 0; i < 16; i++) {
				byteArray[2 * i] = shortArray[i] & 0xff;
				byteArray[2 * i + 1] = shortArray[i] >> 8;
			}

			return byteArray;
		},
		shortArrayToHexString: function(ary) {
			var res = "";
			for (var i = 0; i < ary.length; i++) {
				res += nibbleToChar[(ary[i] >> 4) & 0x0f] + nibbleToChar[ary[i] & 0x0f] + nibbleToChar[(ary[i] >> 12) & 0x0f] + nibbleToChar[(ary[i] >> 8) & 0x0f];
			}
			return res;
		},
		/**
		 * Produces an array of the specified number of bytes to represent the integer
		 * value. Default output encodes ints in little endian format. Handles signed
		 * as well as unsigned integers. Due to limitations in JavaScript's number
		 * format, x cannot be a true 64 bit integer (8 bytes).
		 */
		intToBytes_: function(x, numBytes, unsignedMax, opt_bigEndian) {
			var signedMax = Math.floor(unsignedMax / 2);
			var negativeMax = (signedMax + 1) * -1;
			if (x != Math.floor(x) || x < negativeMax || x > unsignedMax) {
				throw new Error(
					x + ' is not a ' + (numBytes * 8) + ' bit integer');
			}
			var bytes = [];
			var current;
			// Number type 0 is in the positive int range, 1 is larger than signed int,
			// and 2 is negative int.
			var numberType = x >= 0 && x <= signedMax ? 0 :
				x > signedMax && x <= unsignedMax ? 1 : 2;
			if (numberType == 2) {
				x = (x * -1) - 1;
			}
			for (var i = 0; i < numBytes; i++) {
				if (numberType == 2) {
					current = 255 - (x % 256);
				} else {
					current = x % 256;
				}

				if (opt_bigEndian) {
					bytes.unshift(current);
				} else {
					bytes.push(current);
				}

				if (numberType == 1) {
					x = Math.floor(x / 256);
				} else {
					x = x >> 8;
				}
			}
			return bytes;

		},
		int32ToBytes: function(x, opt_bigEndian) {
			return converters.intToBytes_(x, 4, 4294967295, opt_bigEndian);
		}
	}
}();
// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if(a != null)
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
}

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}
if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+this.DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { this.fromRadix(s,b); return; }
  this.t = 0;
  this.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      this[this.t++] = x;
    else if(sh+k > this.DB) {
      this[this.t-1] |= (x&((1<<(this.DB-sh))-1))<<sh;
      this[this.t++] = (x>>(this.DB-sh));
    }
    else
      this[this.t-1] |= x<<sh;
    sh += k;
    if(sh >= this.DB) sh -= this.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    this.s = -1;
    if(sh > 0) this[this.t-1] |= ((1<<(this.DB-sh))-1)<<sh;
  }
  this.clamp();
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  if(this.s < 0) return "-"+this.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return this.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = this.t;
  var p = this.DB-(i*this.DB)%k;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (this[i]&((1<<p)-1))<<(k-p);
        d |= this[--i]>>(p+=this.DB-k);
      }
      else {
        d = (this[i]>>(p-=k))&km;
        if(p <= 0) { p += this.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return (this.s<0)?-r:r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/this.DB), c = (this.s<<bs)&this.DM, i;
  for(i = this.t-1; i >= 0; --i) {
    r[i+ds+1] = (this[i]>>cbs)|c;
    c = (this[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = this.t+ds+1;
  r.s = this.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  r.s = this.s;
  var ds = Math.floor(n/this.DB);
  if(ds >= this.t) { r.t = 0; return; }
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = this[ds]>>bs;
  for(var i = ds+1; i < this.t; ++i) {
    r[i-ds-1] |= (this[i]&bm)<<cbs;
    r[i-ds] = this[i]>>bs;
  }
  if(bs > 0) r[this.t-ds-1] |= (this.s&bm)<<cbs;
  r.t = this.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]-a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c -= a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = this.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = this.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) this.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = this.s, ms = m.s;
  var nsh = this.DB-nbits(pm[pm.t-1]);	// normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<this.F1)+((ys>1)?y[ys-2]>>this.F2:0);
  var d1 = this.FV/yt, d2 = (1<<this.F1)/yt, e = 1<<this.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y);	// "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?this.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	// Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);	// Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;		// y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;	// y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;	// y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	// y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;		// y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)	// pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;

// public
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);

// Copyright (c) 2005-2009  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Extended JavaScript BN functions, required for RSA private ops.

// Version 1.1: new BigInteger("0", 10) returns "proper" zero
// Version 1.2: square() API, isProbablePrime fix

// (public)
function bnClone() { var r = nbi(); this.copyTo(r); return r; }

// (public) return value as integer
function bnIntValue() {
  if(this.s < 0) {
    if(this.t == 1) return this[0]-this.DV;
    else if(this.t == 0) return -1;
  }
  else if(this.t == 1) return this[0];
  else if(this.t == 0) return 0;
  // assumes 16 < DB < 32
  return ((this[1]&((1<<(32-this.DB))-1))<<this.DB)|this[0];
}

// (public) return value as byte
function bnByteValue() { return (this.t==0)?this.s:(this[0]<<24)>>24; }

// (public) return value as short (assumes DB>=16)
function bnShortValue() { return (this.t==0)?this.s:(this[0]<<16)>>16; }

// (protected) return x s.t. r^x < DV
function bnpChunkSize(r) { return Math.floor(Math.LN2*this.DB/Math.log(r)); }

// (public) 0 if this == 0, 1 if this > 0
function bnSigNum() {
  if(this.s < 0) return -1;
  else if(this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
  else return 1;
}

// (protected) convert to radix string
function bnpToRadix(b) {
  if(b == null) b = 10;
  if(this.signum() == 0 || b < 2 || b > 36) return "0";
  var cs = this.chunkSize(b);
  var a = Math.pow(b,cs);
  var d = nbv(a), y = nbi(), z = nbi(), r = "";
  this.divRemTo(d,y,z);
  while(y.signum() > 0) {
    r = (a+z.intValue()).toString(b).substr(1) + r;
    y.divRemTo(d,y,z);
  }
  return z.intValue().toString(b) + r;
}

// (protected) convert from radix string
function bnpFromRadix(s,b) {
  this.fromInt(0);
  if(b == null) b = 10;
  var cs = this.chunkSize(b);
  var d = Math.pow(b,cs), mi = false, j = 0, w = 0;
  for(var i = 0; i < s.length; ++i) {
    var x = intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-" && this.signum() == 0) mi = true;
      continue;
    }
    w = b*w+x;
    if(++j >= cs) {
      this.dMultiply(d);
      this.dAddOffset(w,0);
      j = 0;
      w = 0;
    }
  }
  if(j > 0) {
    this.dMultiply(Math.pow(b,j));
    this.dAddOffset(w,0);
  }
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) alternate constructor
function bnpFromNumber(a,b,c) {
  if("number" == typeof b) {
    // new BigInteger(int,int,RNG)
    if(a < 2) this.fromInt(1);
    else {
      this.fromNumber(a,c);
      if(!this.testBit(a-1))	// force MSB set
        this.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,this);
      if(this.isEven()) this.dAddOffset(1,0); // force odd
      while(!this.isProbablePrime(b)) {
        this.dAddOffset(2,0);
        if(this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a-1),this);
      }
    }
  }
  else {
    // new BigInteger(int,RNG)
    var x = new Array(), t = a&7;
    x.length = (a>>3)+1;
    b.nextBytes(x);
    if(t > 0) x[0] &= ((1<<t)-1); else x[0] = 0;
    this.fromString(x,256);
  }
}

// (public) convert to bigendian byte array
function bnToByteArray() {
  var i = this.t, r = new Array();
  r[0] = this.s;
  var p = this.DB-(i*this.DB)%8, d, k = 0;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) != (this.s&this.DM)>>p)
      r[k++] = d|(this.s<<(this.DB-p));
    while(i >= 0) {
      if(p < 8) {
        d = (this[i]&((1<<p)-1))<<(8-p);
        d |= this[--i]>>(p+=this.DB-8);
      }
      else {
        d = (this[i]>>(p-=8))&0xff;
        if(p <= 0) { p += this.DB; --i; }
      }
      if((d&0x80) != 0) d |= -256;
      if(k == 0 && (this.s&0x80) != (d&0x80)) ++k;
      if(k > 0 || d != this.s) r[k++] = d;
    }
  }
  return r;
}

function bnEquals(a) { return(this.compareTo(a)==0); }
function bnMin(a) { return(this.compareTo(a)<0)?this:a; }
function bnMax(a) { return(this.compareTo(a)>0)?this:a; }

// (protected) r = this op a (bitwise)
function bnpBitwiseTo(a,op,r) {
  var i, f, m = Math.min(a.t,this.t);
  for(i = 0; i < m; ++i) r[i] = op(this[i],a[i]);
  if(a.t < this.t) {
    f = a.s&this.DM;
    for(i = m; i < this.t; ++i) r[i] = op(this[i],f);
    r.t = this.t;
  }
  else {
    f = this.s&this.DM;
    for(i = m; i < a.t; ++i) r[i] = op(f,a[i]);
    r.t = a.t;
  }
  r.s = op(this.s,a.s);
  r.clamp();
}

// (public) this & a
function op_and(x,y) { return x&y; }
function bnAnd(a) { var r = nbi(); this.bitwiseTo(a,op_and,r); return r; }

// (public) this | a
function op_or(x,y) { return x|y; }
function bnOr(a) { var r = nbi(); this.bitwiseTo(a,op_or,r); return r; }

// (public) this ^ a
function op_xor(x,y) { return x^y; }
function bnXor(a) { var r = nbi(); this.bitwiseTo(a,op_xor,r); return r; }

// (public) this & ~a
function op_andnot(x,y) { return x&~y; }
function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

// (public) ~this
function bnNot() {
  var r = nbi();
  for(var i = 0; i < this.t; ++i) r[i] = this.DM&~this[i];
  r.t = this.t;
  r.s = ~this.s;
  return r;
}

// (public) this << n
function bnShiftLeft(n) {
  var r = nbi();
  if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
  return r;
}

// (public) this >> n
function bnShiftRight(n) {
  var r = nbi();
  if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
  return r;
}

// return index of lowest 1-bit in x, x < 2^31
function lbit(x) {
  if(x == 0) return -1;
  var r = 0;
  if((x&0xffff) == 0) { x >>= 16; r += 16; }
  if((x&0xff) == 0) { x >>= 8; r += 8; }
  if((x&0xf) == 0) { x >>= 4; r += 4; }
  if((x&3) == 0) { x >>= 2; r += 2; }
  if((x&1) == 0) ++r;
  return r;
}

// (public) returns index of lowest 1-bit (or -1 if none)
function bnGetLowestSetBit() {
  for(var i = 0; i < this.t; ++i)
    if(this[i] != 0) return i*this.DB+lbit(this[i]);
  if(this.s < 0) return this.t*this.DB;
  return -1;
}

// return number of 1 bits in x
function cbit(x) {
  var r = 0;
  while(x != 0) { x &= x-1; ++r; }
  return r;
}

// (public) return number of set bits
function bnBitCount() {
  var r = 0, x = this.s&this.DM;
  for(var i = 0; i < this.t; ++i) r += cbit(this[i]^x);
  return r;
}

// (public) true iff nth bit is set
function bnTestBit(n) {
  var j = Math.floor(n/this.DB);
  if(j >= this.t) return(this.s!=0);
  return((this[j]&(1<<(n%this.DB)))!=0);
}

// (protected) this op (1<<n)
function bnpChangeBit(n,op) {
  var r = BigInteger.ONE.shiftLeft(n);
  this.bitwiseTo(r,op,r);
  return r;
}

// (public) this | (1<<n)
function bnSetBit(n) { return this.changeBit(n,op_or); }

// (public) this & ~(1<<n)
function bnClearBit(n) { return this.changeBit(n,op_andnot); }

// (public) this ^ (1<<n)
function bnFlipBit(n) { return this.changeBit(n,op_xor); }

// (protected) r = this + a
function bnpAddTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]+a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c += a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c += a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += a.s;
  }
  r.s = (c<0)?-1:0;
  if(c > 0) r[i++] = c;
  else if(c < -1) r[i++] = this.DV+c;
  r.t = i;
  r.clamp();
}

// (public) this + a
function bnAdd(a) { var r = nbi(); this.addTo(a,r); return r; }

// (public) this - a
function bnSubtract(a) { var r = nbi(); this.subTo(a,r); return r; }

// (public) this * a
function bnMultiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

// (public) this^2
function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

// (public) this / a
function bnDivide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

// (public) this % a
function bnRemainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

// (public) [this/a,this%a]
function bnDivideAndRemainder(a) {
  var q = nbi(), r = nbi();
  this.divRemTo(a,q,r);
  return new Array(q,r);
}

// (protected) this *= n, this >= 0, 1 < n < DV
function bnpDMultiply(n) {
  this[this.t] = this.am(0,n-1,this,0,0,this.t);
  ++this.t;
  this.clamp();
}

// (protected) this += n << w words, this >= 0
function bnpDAddOffset(n,w) {
  if(n == 0) return;
  while(this.t <= w) this[this.t++] = 0;
  this[w] += n;
  while(this[w] >= this.DV) {
    this[w] -= this.DV;
    if(++w >= this.t) this[this.t++] = 0;
    ++this[w];
  }
}

// A "null" reducer
function NullExp() {}
function nNop(x) { return x; }
function nMulTo(x,y,r) { x.multiplyTo(y,r); }
function nSqrTo(x,r) { x.squareTo(r); }

NullExp.prototype.convert = nNop;
NullExp.prototype.revert = nNop;
NullExp.prototype.mulTo = nMulTo;
NullExp.prototype.sqrTo = nSqrTo;

// (public) this^e
function bnPow(e) { return this.exp(e,new NullExp()); }

// (protected) r = lower n words of "this * a", a.t <= n
// "this" should be the larger one if appropriate.
function bnpMultiplyLowerTo(a,n,r) {
  var i = Math.min(this.t+a.t,n);
  r.s = 0; // assumes a,this >= 0
  r.t = i;
  while(i > 0) r[--i] = 0;
  var j;
  for(j = r.t-this.t; i < j; ++i) r[i+this.t] = this.am(0,a[i],r,i,0,this.t);
  for(j = Math.min(a.t,n); i < j; ++i) this.am(0,a[i],r,i,0,n-i);
  r.clamp();
}

// (protected) r = "this * a" without lower n words, n > 0
// "this" should be the larger one if appropriate.
function bnpMultiplyUpperTo(a,n,r) {
  --n;
  var i = r.t = this.t+a.t-n;
  r.s = 0; // assumes a,this >= 0
  while(--i >= 0) r[i] = 0;
  for(i = Math.max(n-this.t,0); i < a.t; ++i)
    r[this.t+i-n] = this.am(n-i,a[i],r,0,0,this.t+i-n);
  r.clamp();
  r.drShiftTo(1,r);
}

// Barrett modular reduction
function Barrett(m) {
  // setup Barrett
  this.r2 = nbi();
  this.q3 = nbi();
  BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
  this.mu = this.r2.divide(m);
  this.m = m;
}

function barrettConvert(x) {
  if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
  else if(x.compareTo(this.m) < 0) return x;
  else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
}

function barrettRevert(x) { return x; }

// x = x mod m (HAC 14.42)
function barrettReduce(x) {
  x.drShiftTo(this.m.t-1,this.r2);
  if(x.t > this.m.t+1) { x.t = this.m.t+1; x.clamp(); }
  this.mu.multiplyUpperTo(this.r2,this.m.t+1,this.q3);
  this.m.multiplyLowerTo(this.q3,this.m.t+1,this.r2);
  while(x.compareTo(this.r2) < 0) x.dAddOffset(1,this.m.t+1);
  x.subTo(this.r2,x);
  while(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = x^2 mod m; x != r
function barrettSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = x*y mod m; x,y != r
function barrettMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Barrett.prototype.convert = barrettConvert;
Barrett.prototype.revert = barrettRevert;
Barrett.prototype.reduce = barrettReduce;
Barrett.prototype.mulTo = barrettMulTo;
Barrett.prototype.sqrTo = barrettSqrTo;

// (public) this^e % m (HAC 14.85)
function bnModPow(e,m) {
  var i = e.bitLength(), k, r = nbv(1), z;
  if(i <= 0) return r;
  else if(i < 18) k = 1;
  else if(i < 48) k = 3;
  else if(i < 144) k = 4;
  else if(i < 768) k = 5;
  else k = 6;
  if(i < 8)
    z = new Classic(m);
  else if(m.isEven())
    z = new Barrett(m);
  else
    z = new Montgomery(m);

  // precomputation
  var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
  g[1] = z.convert(this);
  if(k > 1) {
    var g2 = nbi();
    z.sqrTo(g[1],g2);
    while(n <= km) {
      g[n] = nbi();
      z.mulTo(g2,g[n-2],g[n]);
      n += 2;
    }
  }

  var j = e.t-1, w, is1 = true, r2 = nbi(), t;
  i = nbits(e[j])-1;
  while(j >= 0) {
    if(i >= k1) w = (e[j]>>(i-k1))&km;
    else {
      w = (e[j]&((1<<(i+1))-1))<<(k1-i);
      if(j > 0) w |= e[j-1]>>(this.DB+i-k1);
    }

    n = k;
    while((w&1) == 0) { w >>= 1; --n; }
    if((i -= n) < 0) { i += this.DB; --j; }
    if(is1) {	// ret == 1, don't bother squaring or multiplying it
      g[w].copyTo(r);
      is1 = false;
    }
    else {
      while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
      if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
      z.mulTo(r2,g[w],r);
    }

    while(j >= 0 && (e[j]&(1<<i)) == 0) {
      z.sqrTo(r,r2); t = r; r = r2; r2 = t;
      if(--i < 0) { i = this.DB-1; --j; }
    }
  }
  return z.revert(r);
}

// (public) gcd(this,a) (HAC 14.54)
function bnGCD(a) {
  var x = (this.s<0)?this.negate():this.clone();
  var y = (a.s<0)?a.negate():a.clone();
  if(x.compareTo(y) < 0) { var t = x; x = y; y = t; }
  var i = x.getLowestSetBit(), g = y.getLowestSetBit();
  if(g < 0) return x;
  if(i < g) g = i;
  if(g > 0) {
    x.rShiftTo(g,x);
    y.rShiftTo(g,y);
  }
  while(x.signum() > 0) {
    if((i = x.getLowestSetBit()) > 0) x.rShiftTo(i,x);
    if((i = y.getLowestSetBit()) > 0) y.rShiftTo(i,y);
    if(x.compareTo(y) >= 0) {
      x.subTo(y,x);
      x.rShiftTo(1,x);
    }
    else {
      y.subTo(x,y);
      y.rShiftTo(1,y);
    }
  }
  if(g > 0) y.lShiftTo(g,y);
  return y;
}

// (protected) this % n, n < 2^26
function bnpModInt(n) {
  if(n <= 0) return 0;
  var d = this.DV%n, r = (this.s<0)?n-1:0;
  if(this.t > 0)
    if(d == 0) r = this[0]%n;
    else for(var i = this.t-1; i >= 0; --i) r = (d*r+this[i])%n;
  return r;
}

// (public) 1/this % m (HAC 14.61)
function bnModInverse(m) {
  var ac = m.isEven();
  if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
  var u = m.clone(), v = this.clone();
  var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
  while(u.signum() != 0) {
    while(u.isEven()) {
      u.rShiftTo(1,u);
      if(ac) {
        if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
        a.rShiftTo(1,a);
      }
      else if(!b.isEven()) b.subTo(m,b);
      b.rShiftTo(1,b);
    }
    while(v.isEven()) {
      v.rShiftTo(1,v);
      if(ac) {
        if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
        c.rShiftTo(1,c);
      }
      else if(!d.isEven()) d.subTo(m,d);
      d.rShiftTo(1,d);
    }
    if(u.compareTo(v) >= 0) {
      u.subTo(v,u);
      if(ac) a.subTo(c,a);
      b.subTo(d,b);
    }
    else {
      v.subTo(u,v);
      if(ac) c.subTo(a,c);
      d.subTo(b,d);
    }
  }
  if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
  if(d.compareTo(m) >= 0) return d.subtract(m);
  if(d.signum() < 0) d.addTo(m,d); else return d;
  if(d.signum() < 0) return d.add(m); else return d;
}

var lowprimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997];
var lplim = (1<<26)/lowprimes[lowprimes.length-1];

// (public) test primality with certainty >= 1-.5^t
function bnIsProbablePrime(t) {
  var i, x = this.abs();
  if(x.t == 1 && x[0] <= lowprimes[lowprimes.length-1]) {
    for(i = 0; i < lowprimes.length; ++i)
      if(x[0] == lowprimes[i]) return true;
    return false;
  }
  if(x.isEven()) return false;
  i = 1;
  while(i < lowprimes.length) {
    var m = lowprimes[i], j = i+1;
    while(j < lowprimes.length && m < lplim) m *= lowprimes[j++];
    m = x.modInt(m);
    while(i < j) if(m%lowprimes[i++] == 0) return false;
  }
  return x.millerRabin(t);
}

// (protected) true if probably prime (HAC 4.24, Miller-Rabin)
function bnpMillerRabin(t) {
  var n1 = this.subtract(BigInteger.ONE);
  var k = n1.getLowestSetBit();
  if(k <= 0) return false;
  var r = n1.shiftRight(k);
  t = (t+1)>>1;
  if(t > lowprimes.length) t = lowprimes.length;
  var a = nbi();
  for(var i = 0; i < t; ++i) {
    //Pick bases at random, instead of starting at 2
    a.fromInt(lowprimes[Math.floor(Math.random()*lowprimes.length)]);
    var y = a.modPow(r,this);
    if(y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
      var j = 1;
      while(j++ < k && y.compareTo(n1) != 0) {
        y = y.modPowInt(2,this);
        if(y.compareTo(BigInteger.ONE) == 0) return false;
      }
      if(y.compareTo(n1) != 0) return false;
    }
  }
  return true;
}

// protected
BigInteger.prototype.chunkSize = bnpChunkSize;
BigInteger.prototype.toRadix = bnpToRadix;
BigInteger.prototype.fromRadix = bnpFromRadix;
BigInteger.prototype.fromNumber = bnpFromNumber;
BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
BigInteger.prototype.changeBit = bnpChangeBit;
BigInteger.prototype.addTo = bnpAddTo;
BigInteger.prototype.dMultiply = bnpDMultiply;
BigInteger.prototype.dAddOffset = bnpDAddOffset;
BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
BigInteger.prototype.modInt = bnpModInt;
BigInteger.prototype.millerRabin = bnpMillerRabin;

// public
BigInteger.prototype.clone = bnClone;
BigInteger.prototype.intValue = bnIntValue;
BigInteger.prototype.byteValue = bnByteValue;
BigInteger.prototype.shortValue = bnShortValue;
BigInteger.prototype.signum = bnSigNum;
BigInteger.prototype.toByteArray = bnToByteArray;
BigInteger.prototype.equals = bnEquals;
BigInteger.prototype.min = bnMin;
BigInteger.prototype.max = bnMax;
BigInteger.prototype.and = bnAnd;
BigInteger.prototype.or = bnOr;
BigInteger.prototype.xor = bnXor;
BigInteger.prototype.andNot = bnAndNot;
BigInteger.prototype.not = bnNot;
BigInteger.prototype.shiftLeft = bnShiftLeft;
BigInteger.prototype.shiftRight = bnShiftRight;
BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
BigInteger.prototype.bitCount = bnBitCount;
BigInteger.prototype.testBit = bnTestBit;
BigInteger.prototype.setBit = bnSetBit;
BigInteger.prototype.clearBit = bnClearBit;
BigInteger.prototype.flipBit = bnFlipBit;
BigInteger.prototype.add = bnAdd;
BigInteger.prototype.subtract = bnSubtract;
BigInteger.prototype.multiply = bnMultiply;
BigInteger.prototype.divide = bnDivide;
BigInteger.prototype.remainder = bnRemainder;
BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
BigInteger.prototype.modPow = bnModPow;
BigInteger.prototype.modInverse = bnModInverse;
BigInteger.prototype.pow = bnPow;
BigInteger.prototype.gcd = bnGCD;
BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

// JSBN-specific extension
BigInteger.prototype.square = bnSquare;

// BigInteger interfaces not implemented in jsbn:

// BigInteger(int signum, byte[] magnitude)
// double doubleValue()
// float floatValue()
// int hashCode()
// long longValue()
// static BigInteger valueOf(long val)

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

(function(){var DEFAULT_NODE = "jnxt.org";

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


	 function getPublicKey(secretPhrase) {
		
			var secretPhraseBytes = converters.stringToByteArray(secretPhrase);
			var digest = simpleHash(secretPhraseBytes);
			return curve25519.keygen(digest).p;
	}


	 function getAccountIdFromPublicKey(publicKey, RSFormat) {
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

	function areByteArraysEqual(bytes1, bytes2) {
		if (bytes1.length !== bytes2.length)
			return false;

		for (var i = 0; i < bytes1.length; ++i) {
			if (bytes1[i] !== bytes2[i])
				return false;
		}

		return true;
	}

	
	 function verifyBytes(signature, message, publicKey) {
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

	 function signBytes(message, secretPhrase) {
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

		return (v.concat(h));
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

function generateToken(websiteString, secretPhrase)
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

        var sig = signBytes(data, secretPhrase);

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

function parseToken(tokenString, website)
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
       	
        var isValid = verifyBytes(signature, data, publicKey);

        var ret = {};
        ret.isValid = isValid;
        ret.timestamp = timestamp;
        ret.publicKey = converters.byteArrayToHexString(publicKey);

        return ret;

}


function pad(length, val) {
    var array = [];
    for (var i = 0; i < length; i++) {
        array[i] = val;
    }
    return array;
}

function timeago(timestamp)
{
	var fromnow =  currentNxtTime() - timestamp;
		
	var days =  Math.floor(fromnow/86400);
	var hours = Math.floor((fromnow%86400)/3600);
	var minutes = Math.floor((fromnow%3600)/60);
	var seconds = Math.floor(fromnow&60);
	var acc = "";
	if(days != 0 && days != 1) acc = days + " days ago";
	else if(days == 1) acc = " 1 day ago";
	else if(hours != 0 && hours != 1) acc = hours + " hours ago";
	else if(hours == 1) acc = "1 hour ago";
	else if(minutes != 0 && minutes != 1) acc = minutes + " minutes ago";
	else if(minutes == 1) acc = "1 minute ago";
	else if(seconds != 0 && seconds != 1) acc = seconds + " seconds ago";
	else if(seconds == 1) acc = "1 second ago";
	else acc = "just now";
		
	return acc;
}

function esc(str)
{
	return str.replace("&", "&amp").replace("<", "&lt").replace(">", "&gt").replace("\"", "&quot").replace("'", "&#x27;").replace("/", "&#x2F");
}


// 48 -> 57
// 65 -> 90
// 97 -> 122

	/**
	 * Encoders and decoders for base-62 formatted data. Uses the alphabet 0..9 a..z
	 * A..Z, e.g. '0' => 0, 'a' => 10, 'A' => 35 and 'Z' => 61.
	 * 
	 */
	 	var BASE62 = new BigInteger("62");

	  function valueForByte(key) {
	  	var p = key;
		if(p >= 48 && p <= 57)
		{
			return p - 48;
		}
		else if(p >= 65 && p <= 90)
		{
			return p - 65 + 10;
		}
		else if(p >= 97 && p <= 122)
		{
			return p - 97 + 10 + 26;
		}
	    new Error("base62 digit not found");
	    return -1;
	  }

	  /**
	   * Convert a base-62 string known to be a number.
	   * 
	   * @param s
	   * @return
	   */
		function base62Decode(s) {
	    return base62DecodeBytes(converters.stringToByteArray(s));
	  }

	  /**
	   * Convert a base-62 string known to be a number.
	   * 
	   * @param s
	   * @return
	   */
	  	function base62DecodeBytes(bytes) {
	    var res = new BigInteger("0");
	    var multiplier = new BigInteger("1");

	    for (var i = bytes.length - 1; i >= 0; i--) {
	      res = res.add(multiplier.multiply(new BigInteger(valueForByte(bytes[i]).toString())));
	      multiplier = multiplier.multiply(BASE62);
	    }
	    var btr = res.toByteArray();
	    return positiveByteArray(btr);
	  }

function rndstr(len)
{
	var letters = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";
	var ret = "";
	var nums = window.crypto.getRandomValues(new Uint32Array(len));

	for(var a=0;a<len;a++)
	{
		ret += letters[nums[a]%letters.length];
	}
	return ret;
}

function generateSecretPhrase()
{
	return rndstr(6) + "_" + rndstr(6) +  "_" + rndstr(6) + "_" + rndstr(6) + "_" + rndstr(6);
}

function encryptSecretPhrase(phrase, key)
{
	var rkey = prepKey(key);
	return CryptoJS.AES.encrypt(phrase, rkey);
}

function decryptSecretPhrase(cipher, key, checksum)
{
	var rkey = prepKey(key);
	var data = CryptoJS.AES.decrypt(cipher, rkey);

	if(converters.byteArrayToHexString(simpleHash(converters.hexStringToByteArray(data.toString()))) == checksum)
	 return converters.hexStringToString(data.toString());
	else return false;
}

function prepKey(key)
{
	var rounds = 1000;
	var digest = key;
	for(var i=0;i<rounds;i++)
	{
		digest = converters.byteArrayToHexString(simpleHash(digest));
	}
	return digest;
}

function newAccount(secretPhrase, key)
{
	var accountData = {};
	accountData["secretPhrase"] = secretPhrase;
	accountData["publicKey"] = converters.byteArrayToHexString(getPublicKey(accountData["secretPhrase"]));
	accountData["accountRS"] = getAccountIdFromPublicKey(accountData["publicKey"], true);
	accountData["key"] = key;
	accountData["cipher"] = encryptSecretPhrase(accountData["secretPhrase"], key).toString();
	accountData["checksum"] = converters.byteArrayToHexString(simpleHash(converters.stringToByteArray(accountData["secretPhrase"])));
	return accountData;
}

function storeAccount(account)
{ 
	var sto = [];
	if(localStorage["accounts"])
	{
		sto = JSON.parse(localStorage["accounts"]);
	}
	var acc = {};
	acc["accountRS"] = account["accountRS"];
	acc["publicKey"] = account["publicKey"];
	acc["cipher"] = account["cipher"];
	acc["checksum"] = account["checksum"];
	sto.push(acc);

	localStorage["accounts"] = JSON.stringify(sto);
}

var epochNum = 1385294400;
var noAccountsMessage = "No Accounts Added";
var accounts;
var pendingAccount;

function loadAccounts()
{
	clearAccountOptions();
	var accounts = JSON.parse(localStorage["accounts"]);
	if(accounts && accounts.length > 0)
	{
		for(var a=0;a<accounts.length;a++)
		{
			addAccountOption(accounts[a]["accountRS"]);
		}
	}
	else
	{
		addAccountOption(noAccountsMessage);
	}
}

function addAccountOption(option)
{
	if($("#transact_account").html().indexOf(noAccountsMessage) > -1)
	{
		clearAccountOptions();
	}
	$("#transact_account").append("<option>"+option+"</option>");
	$("#token_account").append("<option>"+option+"</option>");
	$("#message_account").append("<option>"+option+"</option>");
	$("#accounts_account").append("<option>"+option+"</option>");
}

function clearAccountOptions()
{
	$("#transact_account").html("");
	$("#token_account").html("");
	$("#message_account").html("");
	$("#accounts_account").html("");
}

function broadcastTransaction(nd, bytes)
{
	var params = {requestType: "broadcastTransaction", transactionBytes: bytes};
	$.ajax(nd, {
		url: nd,
		data: params,
		type: "POST",
		success: transactionBroadcasted,
		timeout: 2000,
		fail: transactionBroadcasted
	});
}

function transactionBroadcasted(resp, state)
{
	var response = JSON.parse(resp);
	$("#modal_signed").modal("hide");
	$("#modal_quick_sure").modal("hide");
	if(state != "success")
	{
		infoModal("Couldn't reach server");
	}
	if(response.errorCode != undefined)
	{
		$("#modal_tx_response_title").text("Transaction Error");
		$("#modal_tx_response_key_1").text("Error Code");
		$("#modal_tx_response_value_1").text(response.errorCode);
		$("#modal_tx_response_key_2").text("Error Description");
		$("#modal_tx_response_value_2").text(response.errorDescription); 
		$("#modal_tx_response").modal("show");

	}
	if(response.transaction != undefined)
	{
		$("#modal_tx_response_title").text("Transaction Successful");
		$("#modal_tx_response_key_1").text("Transaction Id");
		$("#modal_tx_response_value_1").text(response.transaction);
		$("#modal_tx_response_key_2").text("Full Hash");
		$("#modal_tx_response_value_2").text(response.fullHash);
		$("#modal_tx_response").modal("show");
	}
}

function setBroadcastNode(node, isTestnet, isAlwaysSend)
{
    if (node) {
        localStorage["node"] = node;
    }
	localStorage["isTestnet"] = (isTestnet === true);
	Jay.isTestnet = (isTestnet === true);
	localStorage["isAlwaysSend"] = (isAlwaysSend === true);
}

function getBroadcastNode()
{
	var node = "http://";
	if(localStorage["node"] == undefined)
	{
		node += DEFAULT_NODE;
		localStorage["node"] = DEFAULT_NODE;
	}
	else node += localStorage["node"];
	if(localStorage["isTestnet"] == "true") node += ":6876";
	else node += ":7876";
	return node + "/nxt";
}

function pinHandler(source, pin)
{
	if(source == "accounts_new")
	{
		accountsNewHandler(pin);
	}
	else if(source == "change")
	{
		changePinHandler(pin);
	}
	else if(source == "newpin")
	{
		newPinHandler(pin);
	}
	else if(source == "export")
	{
		exportHandler(pin);
	}
	else if(source == "delete")
	{
		deleteHandler(pin);
	}
	else if(source == "import")
	{
		importHandler(pin);
	}
	else if(source == "token")
	{
		tokenHandler(pin);
	}
	else if(source == "quicksend")
	{
		quicksendHandler(pin);
	}
	else if(source == "review")
	{
		reviewHandler(pin);
	}

}

function accountsNewHandler(pin)
{
	$("#modal_accounts_new").modal("show");
	var account = newAccount(generateSecretPhrase(), pin);
	pendingAccount = account;
	$("#modal_accounts_new_address").text(account["accountRS"]);
	$("#modal_accounts_new_recovery").val(account["secretPhrase"]);
}

function changePinHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	var account = findAccount(address);
	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		$("#modal_basic_info").modal("show");
		$("#modal_basic_info_title").text("Incorrect PIN");
	}
	else
	{
		data = undefined;
		$("#modal_enter_pin").data("source", "newpin");
		$("#modal_enter_pin").data("pin", pin);
		setTimeout(function() {$("#modal_enter_pin").modal("show");}, 600);
	}
}

function newPinHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	var accounts = JSON.parse(localStorage["accounts"]);
	var oldpin = $("#modal_enter_pin").data("pin");
	$("#modal_enter_pin").removeAttr("data-pin");


	for(var a=0;a<accounts.length;a++)
	{
		if(accounts[a]["accountRS"] == address)
		{
			// now lets handle...
			var sec = decryptSecretPhrase(accounts[a]["cipher"], oldpin, accounts[a]["checksum"]).toString();
			var newcipher = encryptSecretPhrase(sec, pin).toString();
			accounts[a]["cipher"] = newcipher;
		}
	}
	localStorage["accounts"] = JSON.stringify(accounts);
	infoModal("PIN Change Successful");
}

function exportHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);
	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		$("#modal_export").modal("show");
		$("#modal_export_address").text(account["accountRS"]);
		$("#modal_export_key").val(data);
		data = undefined;
	}
}

function deleteHandler(pin)
{
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);

	var data = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(data === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		$("#modal_delete").modal("show");
		$("#modal_delete_address").text(account["accountRS"]);
		data = undefined;
	}
}

function importHandler(pin)
{
	var secretPhrase = $("#modal_import").data("import");
	$("#modal_import").data("import", "");
	var account = newAccount(secretPhrase, pin);
	storeAccount(account);
	loadAccounts();
	infoModal("Account Successfully Imported");
}

function tokenHandler(pin)
{
	var address = $("#token_account option:selected").text();
	var account = findAccount(address);
	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);
	var websiteString = $("#token_data").val();

	if(secretPhrase === false)
	{
		infoModal("Incorrect PIN");
	}
	else
	{
		var token = generateToken(websiteString, secretPhrase);
		$("#modal_token_box").val(token);
		$("#modal_token").modal("show");
	}
}

function isHex(hex)
{
	for(var a=0;a<hex.length;a++)
	{
		var p = hex.charCodeAt(a)
		if((p < 48) || (p > 57 && p < 65) || (p > 70 && p < 97) || (p > 102))
		{
			return false;
		}
	}
	return true;
}

function startTransact()
{
	var account = $("#transact_account option:selected").val();
	var tx = $("#transact_transaction").val();
	// decide what kind of tx it is
	if(tx.indexOf("NXT-") == 0)
	{
		// nxt addy, quicksend format...
		startQuicksend(account, tx);
	}
	else if(tx.indexOf("TX_") == 0)
	{
		// TRF
		startTRF(account, tx);
	}
	else
	{
		if(isHex(tx))
		{
			// its hex
			if(tx.length == 64)
			{
				startQuicksend(account, tx, true);
			}
			else
			{
				startHex(account, tx);
			}
		}
		else
		{
			infoModal("Transaction Format Unrecognized")
		}
	}
}

function startQuicksend(sender, recipient, pub)
{
	$("#modal_quicksend").modal("show");
	if(pub == undefined || pub == false)
	{
		$("#modal_quicksend_address").val(recipient);
	}
	else if(pub == true)
	{
		var accid = getAccountIdFromPublicKey(recipient, true);
		$("#modal_quicksend_address").val(accid);
	}
	$("#modal_quicksend").data("sender", sender);
	$("#modal_quicksend").data("recipient", recipient);
}

/*255 here..


29 bytes normal tx...
*/

// 0100101234123412341234010000000000000000e1f5050000000000000000
// TX_3YoYmaTiHaxe7ApnLdGR JWnLUnmbB4r9lSsr5pudM

function currentNxtTime()
{
	return Math.floor(Date.now() / 1000) - 1385294400;
}

function nxtTimeBytes()
{
	return converters.int32ToBytes(currentNxtTime());
}

function positiveByteArray(byteArray)
{
	return converters.hexStringToByteArray(converters.byteArrayToHexString(byteArray));
}

function startTRF(sender, trfBytes)
{
	var bytes = base62Decode(trfBytes.substring(3));
	console.log(JSON.stringify(bytes));
	if(bytes[0] == '1')
	{
		bytes = bytes.slice(1);
		if(bytes.length == 31) bytes = bytes.slice(0, 30);

		var collect = [];
		collect = [bytes[0],bytes[1]]; // type ver & subtype
		collect = collect.concat(nxtTimeBytes()); // timestamp
		collect = collect.concat(wordBytes(1440)); // deadline
		var senderPubKey = converters.hexStringToByteArray(findAccount(sender).publicKey);
		collect = collect.concat(senderPubKey);
		collect = collect.concat(bytes.slice(2, 2+8)); // recipient/genesis
		collect = collect.concat(bytes.slice(10, 10+8)); // amount
		collect = collect.concat(bytes.slice(18, 18+8)); // fee
		collect = collect.concat(pad(32, 0)); // reftxhash
		collect = collect.concat(pad(64, 0)); // signature bytes
		collect = collect.concat(bytes.slice(26, 26+4)); // flags
		collect = collect.concat(pad(4, 0)); // EC blockheight
		collect = collect.concat(pad(8, 0)); // EC blockid
		if(bytes.length > 30) collect = collect.concat(bytes.slice(30)); // attachment/appendages
		startHex(converters.byteArrayToHexString(collect));
	}


}

function startHex(hex)
{
	// now we have hex bytes, lets deal with them...
	var bytes = converters.hexStringToByteArray(hex);

	// get important things from this, verify it?..
	extractBytesData(bytes);
}

function clearReview()
{
	setReview(1, "", "");
	setReview(2, "", "");
	setReview(3, "", "");
	setReview(4, "", "");
	setReview(5, "", "");
	setReview(6, "", "");

	$("#tx_desc").html("");
	$("#tx_sender_title").text("");
	$("#tx_fee").text("");
	$("#tx_sender").text("");

	$("#detailtx_loading").hide();
	$("#detailtx_button").hide();
	$("#detailtx_button").unbind("click");
}

function extractBytesData(bytes)
{
	// lets think here.
	// first we take out the version and subversion, and then think from there
	// have about 8 different places to put data, then account for all possible types
	// appendages will have dropdowns with their content and won't take up much room.
	// the 8 zones will need to be really small.
	// type sender amount recip extra for attachment...
	clearReview();
	$("#modal_review_description").attr("disabled", "true");
	$("#modal_review_description").attr("data-content", "");
	$("#modal_review").data("bytes", converters.byteArrayToHexString(bytes));
	var type = bytes[0];
	var subtype = bytes[1] % 16;
	var sender = getAccountIdFromPublicKey(converters.byteArrayToHexString(bytes.slice(8, 8+32)), true);
	var r = new NxtAddress();
	r.set(byteArrayToBigInteger(bytes.slice(40, 48)).toString());
	var recipient = r.toString();
	var amount = byteArrayToBigInteger(bytes.slice(48, 48+8));
	var fee = byteArrayToBigInteger(bytes.slice(56, 56+8));
	var flags = converters.byteArrayToSignedInt32(bytes.slice(160, 160+4));
	rest = [];
	if(bytes.length > 176) rest = bytes.slice(176);
	var msg = [];
	if(type == 0)
	{
		if(subtype == 0)
		{
		    $("#tx_desc").html("Send <b>" + amount / 100000000 + " NXT</b> to <b>" + recipient + "</b>");
		    $("#tx_sender_title").text("Sender");
		    
			typeName = "Ordinary Payment";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			setReview(4, "Amount", amount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length) msg = rest;
		}
	}
	else if(type == 1)
	{
		if(subtype == 0)
		{
		    $("#tx_desc").html("Send message to <b>" + recipient + "</b>");
		    $("#tx_sender_title").text("Sender");

			typeName = "Arbitrary Message";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length) msg = rest;
		}
		else if(subtype == 1) 
		{
			typeName = "Alias Assignment";
			setReview(1, "Type", typeName);
			setReview(2, "Registrar", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(3, "Alias Name", alias);
			setReview(4, "Fee", fee/100000000 + " nxt");
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			if(rest.length > 2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1]))) msg = rest.slice(2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1])));

			$("#tx_desc").html("Create/update alias <b>" + alias + "</b>");
			$("#tx_sender_title").text("Registrar");
		}
		else if(subtype == 2)
		{
			typeName = "Poll Creation"; //  not yet
		}
		else if(subtype == 3) 
		{
			typeName = "Vote Casting"; // not yet
		}
		else if(subtype == 4)
		{
			typeName = "Hub Announcement"; //  what even is this?
		}
		else if(subtype == 5) 
		{
			typeName = "Account Info";
			setReview(1, "Type", typeName);
			setReview(2, "Account", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(3, "Name", alias);
			setReview(4, "Fee", fee/100000000 + " nxt");
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			if(rest.length > 2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1]))) msg = rest.slice(2+rest[1]+bytesWord(rest.slice(2+rest[1], 4+rest[1])));

			$("#tx_desc").html("Set <b>" + alias + "</b> as your account's name");
			$("#tx_sender_title").text("Account");
		}
		else if(subtype == 6) 
		{
			typeName = "Alias Sell";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			var target = "";
			if (recipient == "NXT-MRCC-2YLS-8M54-3CMAJ") { setReview(3, "Buyer", "Anyone"); target = "anyone"; }
			else { setReview(3, "Buyer", recipient); target = recipient; }
			setReview(4, "Alias Name", alias);
			var price = byteArrayToBigInteger(rest.slice(2 + rest[1], 10 + rest[1])).toString();
			price = price/100000000;
			setReview(5, "Sell Price", price);
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 10+rest[1]) msg = rest.slice(10+rest[1]);

			$("#tx_desc").html("Sell alias <b>" + alias + "</b> to <b>" + target + "</b> for <b>" + price + " NXT</b>");
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 7) 
		{
			typeName = "Alias Buy";
			setReview(1, "Type", typeName);
			setReview(2, "Buyer", sender);
			setReview(3, "Seller", recipient);
			var alias = converters.byteArrayToString(rest.slice(2, rest[1]+2));
			setReview(4, "Alias", alias);
			setReview(5, "Buy Price", amount/100000000 + " nxt");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 2+rest[1]) msg = rest.slice(2+rest[1]);

			$("#tx_desc").html("Buy alias <b>" + alias + "</b> from <b>" + recipient + "</b> for <b>" + amount/100000000 + " NXT</b>");
			$("#tx_sender_title").text("Buyer");
		}
	}
	else if(type == 2)
	{
		if(subtype == 0) 
		{
			typeName = "Asset Issuance";
			setReview(1, "Type", typeName);
			setReview(2, "Issuer", sender);
			var name = converters.byteArrayToString(rest.slice(2,rest[1]+2));
			setReview(3, "Asset Name", name);
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			var newpos = 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]]);
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			var units = byteArrayToBigInteger(rest.slice(newpos, newpos+8));
			var decimals = rest[newpos+8];
			units = units/Math.pow(10, decimals);
			setReview(4, "Units", units);
			setReview(5, "Decimals", decimals);
			setReview(6, "Fee", fee/100000000 + " nxt");

			$("#tx_desc").html("Issue <b>" + units + " units</b> asset <b>" + name + "</b>, with decimal <b>" + decimals + "</b>");
			$("#tx_sender_title").text("Issuer");
		}
		else if(subtype == 1) 
		{
			typeName = "Asset Transfer";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(5, "Amount", amount + " QNT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);

			function assetTransfer_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount/Math.pow(10, data.decimals);
			            $("#tx_desc").html("Transfer <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> to <b>" + recipient + "</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, assetTransfer_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Transfer <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> to <b>" + recipient + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, assetTransfer_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Sender");
		}
		else if(subtype == 2) 
		{
			typeName = "Ask Order Placement";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount", amount + " QNT");
			var price = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(5, "Price", price + " NQT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 25) msg = rest.slice(25);

			function askOrderPlacement_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount / Math.pow(10, data.decimals);
			            price = price / Math.pow(10, 8 - data.decimals);
			            $("#tx_desc").html("Sell <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, askOrderPlacement_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Sell <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> at <b>" + price +" NQT </b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, askOrderPlacement_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 3) 
		{
			typeName = "Bid Order Placement";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var assetId = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Asset Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount", amount + " QNT");
			var price = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(5, "Price", price + " NQT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 25) msg = rest.slice(25);

			function bidOrderPlacement_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            amount = amount / Math.pow(10, data.decimals);
			            price = price / Math.pow(10, 8 - data.decimals);
			            $("#tx_desc").html("Buy <b>" + amount + " </b> asset <b>" + data.name + " (" + assetId + ")</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAsset", { "asset": assetId }, bidOrderPlacement_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Buy <b>" + amount + " QNT</b> asset <b>" + assetId + "</b> at <b>" + price + " NQT </b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAsset", { "asset": assetId }, bidOrderPlacement_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 4) 
		{
			typeName = "Ask Order Cancellation";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Order Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			var quantityQNT, priceNQT;
			function getAskOrder_OnSuccess(data, status, xhr) {
			    try {
			        if (data.hasOwnProperty('asset')) {
			            quantityQNT = data.quantityQNT;
			            priceNQT = data.priceNQT;
			            getDetailTx("getAsset", { "asset": data.asset }, getAskOrderGetAsset_OnSuccess);
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			function getAskOrderGetAsset_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            var quantity = quantityQNT / Math.pow(10, Number(data.decimals));
			            var price = priceNQT / Math.pow(10, 8 - Number(data.decimals));
			            $("#tx_desc").html("Cancel ask order <b>" + order + "</b> - " + "Sell <b>" + quantity + " </b> asset <b>" + esc(data.name) + "</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getAskOrder", { "order": order }, getAskOrder_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Cancel ask order <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getAskOrder", { "order": order }, getAskOrder_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
		else if(subtype == 5)
		{
			typeName = "Bid Order Cancellation";
			setReview(1, "Type", typeName);
			setReview(2, "Trader", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Order Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			var quantityQNT, priceNQT;
			function getBidOrder_OnSuccess(data, status, xhr) {
			    try {
			        if (data.hasOwnProperty('asset')) {
			            quantityQNT = Number(data.quantityQNT);
			            priceNQT = Number(data.priceNQT);
			            getDetailTx("getAsset", { "asset": data.asset }, getBidOrderGetAsset_OnSuccess);
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			function getBidOrderGetAsset_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('decimals')) {
			            var quantity = quantityQNT / Math.pow(10, Number(data.decimals));
			            var price = priceNQT / Math.pow(10, 8 - Number(data.decimals));
			            $("#tx_desc").html("Cancel bid order <b>" + order + "</b> - " + "Buy <b>" + quantity + " </b> asset <b>" + esc(data.name) + "</b> at <b>" + price + " NXT </b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getBidOrder", { "order": order }, getBidOrder_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Cancel bid order <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getBidOrder", { "order": order }, getBidOrder_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Trader");
		}
	}
	else if(type == 3)
	{
		if(subtype == 0) 
		{
			typeName = "Goods Listing";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var name = converters.byteArrayToString(rest.slice(3,rest[1]+2));
			setReview(3, "Good Name", name);
			var data = converters.byteArrayToString(rest.slice(4+rest[1], 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]])));
			var newpos = 4+rest[1]+bytesWord([rest[2+rest[1]], rest[3+rest[1]]]);
			var tags = converters.byteArrayToString(rest.slice(newpos+2, newpos+2+bytesWord([rest[newpos],rest[newpos+1]])));
			newpos = newpos+2+bytesWord([rest[newpos],rest[newpos+1]]);
			setReview(4, "Tags", tags);
			$("#modal_review_description").removeAttr("disabled");
			$("#modal_review_description").attr("data-content", data);
			var amount = converters.byteArrayToSignedInt32(rest.slice(newpos, newpos+4));
			var price = byteArrayToBigInteger(rest.slice(newpos+4, newpos+12)).toString();
			setReview(5, "Amount (price)", amount + "(" + price/100000000 + " nxt)");
			setReview(6, "Fee", fee/100000000 + " nxt");
		}
		else if(subtype == 1) 
		{
			typeName = "Goods Delisting";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var order = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", order);
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 9) msg = rest.slice(9);

			function goodDelisting_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            var price = Number(data.priceNQT) / 100000000;
			            $("#tx_desc").html("Delete marketplace product <b>" + order + "</b> : <br/><br/>" + '<table class="table table-striped"><tbody><tr><th style="width:85px"><strong>Product</strong>:</th><td>' + esc(data.name) + '</td></tr><tr><th><strong>Price</strong>:</th><td>' + price + ' NXT</td></tr><tr><th><strong>Quantity</strong>:</th><td>' + data.quantity + '</td></tr></tbody></table>').show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": order }, goodDelisting_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Delete marketplace product <b>" + order + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": order }, goodDelisting_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 2) 
		{
			typeName = "Price Change";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var newprice = byteArrayToBigInteger(rest.slice(1+8, 1+8+8)).toString();
			setReview(4, "New Price", newprice/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8+8) msg = rest.slice(17);

			function dgsPriceChange_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            var price = Number(data.priceNQT) / 100000000;
			            $("#tx_desc").html("Change price to <b>" + newprice / 100000000 + " NXT</b> for marketplace product <b>" + esc(data.name) + " (" + goodid + ")</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsPriceChange_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Change price to <b>" + newprice / 100000000 + " NXT</b> for marketplace product <b>" + goodid + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsPriceChange_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 3) 
		{
			typeName = "Quantity Change";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var chg = converters.byteArrayToSignedInt32(rest.slice(1+8, 1+8+4));
			if(chg < 0) setReview(4, "Decrease By", -chg);
			else setReview(4, "Increase By", chg);
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8+4) msg = rest.slice(13);

			function dgsQuantityChange_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            $("#tx_desc").html("Change quantity to <b>" + chg + "</b> for marketplace product <b>" + esc(data.name) + " (" + goodid + ")</b>").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsQuantityChange_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Change quantity to <b>" + chg + "</b> for marketplace product <b>" + goodid + "</b>").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsQuantityChange_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 4)
		{
			typeName = "Purchase";
			setReview(1, "Type", typeName);
			setReview(2, "Buyer", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var qnt = byteArrayToBigInteger(rest.slice(1+8, 1+8+4)).toString();
			setReview(4, "Quantity", qnt);
			var price = byteArrayToBigInteger(rest.slice(1+8+4, 1+16+4)).toString();
			setReview(5, "Price", price/100000000 + " nxt");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+16+8) msg = rest.slice(25);

			function dgsPurchase_OnSuccess(data, status, xhr) {
			    $("#detailtx_loading").hide();
			    try {
			        if (data.hasOwnProperty('name')) {
			            $("#tx_desc").html("Purchase <b>" + qnt + "</b> product <b>" + esc(data.name) + " (" + goodid + ")</b> at <b>" + price / 100000000 + " NXT</b> each").show();
			        } else {
			            getDetailTx_OnFail(data);
			        }
			    }
			    catch (err) {
			        getDetailTx_OnFail();
			    }
			}

			if (isGetTxDetails()) {
			    getDetailTx("getDGSGood", { "goods": goodid }, dgsPurchase_OnSuccess);
			}
			else {
			    $("#tx_desc").html("Purchase <b>" + qnt + "</b> product <b>" + goodid + "</b> at <b>" + price / 100000000 + " NXT</b> each").show();
			    $("#detailtx_button").bind("click", function () {
			        getDetailTx("getDGSGood", { "goods": goodid }, dgsPurchase_OnSuccess);
			        $("#detailtx_button").hide();
			        $("#detailtx_loading").show();
			        $("#tx_desc").hide();
			    }).show();
			}
			$("#tx_sender_title").text("Seller");
		}
		else if(subtype == 5)
		{
			typeName = "Delivery";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Item Id", goodid);
			var discount = byteArrayToBigInteger(rest.slice(rest.length-8)).toString();
			setReview(4, "Discount", discount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8) msg = rest.slice(9);
		
		}
		else if(subtype == 6) 
		{
			typeName = "Feedback";
			setReview(1, "Type", typeName);
			setReview(2, "User", sender);
			setReview(3, "Seller", recipient);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Item Id", goodid);
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+8) msg = rest.slice(9);
		}
		else if(subtype == 7) 
		{
			typeName = "Refund";
			setReview(1, "Type", typeName);
			setReview(2, "Seller", sender);
			var goodid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Purchase Id", goodid);
			var discount = byteArrayToBigInteger(rest.slice(1+8,1+16)).toString();
			setReview(4, "Refund Amount", discount/100000000 + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 1+16) msg = rest.slice(17);
		}
	}
	else if(type == 4)
	{
		if(subtype == 0)
		{
			typeName = "Balance Leasing";
			setReview(1, "Type", typeName);
			setReview(2, "Lessor", sender);
			var lease = bytesWord(rest.slice(1,3));
			setReview(3, "Length", lease + " blocks");
			setReview(4, "Fee", fee/100000000 + " nxt");
			if(rest.length > 3) msg = rest.slice(3);

			$("#tx_desc").html("Lease balance to <b>" + recipient + "</b> for <b>" + lease + " blocks</b>");
			$("#tx_sender_title").text("Sender");
		} 
	}
	else if(type == 5)
	{
		if(subtype == 0)
		{
			typeName = "Issue Currency";
		}
		else if(subtype == 1)
		{
			typeName = "Reserve Increase";
			setReview(1, "Type", typeName);
			setReview(2, "Reserver", sender);
			var assetid = converters.byteArrayToString(rest.slice(1, 1+8));
			setReview(3, "Currency Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(4, "Amount per Unit", amount + " nxt");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);
		}
		else if(subtype == 2)
		{
			typeName = "Reserve Claim";
		}
		else if(subtype == 3)
		{
			typeName = "Currency Transfer";
			setReview(1, "Type", typeName);
			setReview(2, "Sender", sender);
			setReview(3, "Recipient", recipient);
			var ms = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(4, "Currency Id", ms);
			var amount = byteArrayToBigInteger(rest.slice(1+8, 1+16)).toString();
			setReview(5, "Amount", amount + " QNT");
			setReview(6, "Fee", fee/100000000 + " nxt");
			if(rest.length > 17) msg = rest.slice(17);
		}
		else if(subtype == 4)
		{
			typeName = "Exchange Offer";
		}
		else if(subtype == 5)
		{
			typeName = "Exchange Buy";
		}
		else if(subtype == 6)
		{
			typeName = "Exchange Sell";
		}
		else if(subtype == 7)
		{
			typeName = "Mint Currency";
			setReview(1, "Type", typeName);
			setReview(2, "Minter", sender);
			var assetid = byteArrayToBigInteger(rest.slice(1, 1+8)).toString();
			setReview(3, "Currency Id", assetId);
			var amount = byteArrayToBigInteger(rest.slice(1+16, 1+24)).toString();
			setReview(4, "Amount To Mint", amount + " Units");
			setReview(5, "Fee", fee/100000000 + " nxt");
			if(rest.length > 16+16+1) msg = rest.slice(33);
		}
		else if(subtype == 8)
		{
			typeName = "Delete Currency";
		}
	}

	$("#tx_fee").text(fee / 100000000);
	$("#tx_sender").text(sender);

	var message = getModifierBit(flags, 0);
	var publicKey = getModifierBit(flags, 2);
	if(message && msg.length)
	{
		$("#modal_review_message").removeAttr("disabled");
		var len = bytesWord([msg[1],msg[2]]);
		var str = converters.byteArrayToString(msg.slice(5,5+len));
		$("#modal_review_message").attr("data-content", str);
		msg = msg.slice(3+len);
	}
	else $("#modal_review_message").attr("disabled", "true");
	if(publicKey && msg.length)
	{
		$("#modal_review_public_key").removeAttr("disabled");
		var str = converters.byteArrayToHexString(msg.slice(1,65));
		$("#modal_review_public_key").attr("data-content", str);
		msg = msg.slice(65);
	}
	else $("#modal_review_public_key").attr("disabled","true");

	// appendages... ugh... and no icons, how will I do this..

	$("#modal_review").modal("show");
}

function getModifierBit(target, position)
{
	return (target >> position)%2;
}

function setReview(number, key, value)
{
	$("#modal_review_key_"+number).text(key);
	$("#modal_review_value_"+number).text(value);
}


function quicksendHandler(pin)
{
	var amount = $("#modal_enter_pin").data("amount");
	$("#modal_enter_pin").removeAttr("data-amount");
	var recipient = $("#modal_enter_pin").data("recipient");
	$("#modal_enter_pin").removeAttr("data-recipient");
	var sender = $("#modal_enter_pin").data("sender");
	$("#modal_enter_pin").removeAttr("data-sender");
	var account = findAccount(sender)

	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);

	if(secretPhrase === false)
	{
		infoModal("Incorrect PIN");
	}
	else
	{
		var quickbytes = createQuicksend(recipient, amount, secretPhrase);
		$("#modal_quick_sure").data("tx", converters.byteArrayToHexString(quickbytes));
		$("#modal_quick_sure_sender").text(sender);
		if(recipient.indexOf("NXT-") == 0)
		{
			$("#modal_quick_sure_recipient").text(recipient);
		}
		else
		{
			$("#modal_quick_sure_recipient").text(getAccountIdFromPublicKey(recipient, true) + " (with Public Key)");
		}
		$("#modal_quick_sure_amount").text(amount + " NXT");
		$("#modal_quick_sure").modal("show");

		// now we open the "are you sure" modal...tomorrow..
	}
}

function createQuicksend(recipient, amount, secretPhrase)
{
	var txbytes = [];
	txbytes.push(0) // type
	txbytes.push(0 + (1 << 4)); // version/type
	txbytes = txbytes.concat(nxtTimeBytes()); // timestmp
	txbytes = txbytes.concat(wordBytes(1440)); // deadline
	txbytes = txbytes.concat(getPublicKey(secretPhrase)); // public Key

	if(recipient.indexOf("NXT-") == 0)
	{
		recipientRS = recipient;
	}
	else
	{
		recipientRS = getAccountIdFromPublicKey(recipient, true);
	}
	var rec = new NxtAddress();
	rec.set(recipientRS);
	var recip = (new BigInteger(rec.account_id())).toByteArray().reverse();
	if(recip.length == 9) recip = recip.slice(0, 8);
	while(recip.length < 8) recip = recip.concat(pad(1, 0));
	txbytes = txbytes.concat(recip);

	var amt = ((new BigInteger(String(parseInt(amount*100000000))))).toByteArray().reverse();
	if(amt.length == 9) amt = amt.slice(0, 8);
	while(amt.length < 8) amt = amt.concat(pad(1, 0));
	txbytes = txbytes.concat(amt); 

	var fee = (converters.int32ToBytes(100000000));
	while(fee.length < 8) fee = fee.concat(pad(1, 0));
	txbytes = txbytes.concat(fee);

	txbytes = txbytes.concat(pad(32, 0)); // ref full hash
	txbytes = txbytes.concat(pad(64, 0)); // signature

	if(recipient.indexOf("NXT-") == 0)
	{
		txbytes = txbytes.concat(pad(16, 0)); // ignore everything else
	}
	else
	{
		txbytes.push(4);
		txbytes = txbytes.concat(pad(3, 0));
		txbytes = txbytes.concat(pad(12, 0));
		txbytes = txbytes.concat([1]);
		txbytes = txbytes.concat(converters.hexStringToByteArray(recipient));
	}

	txbytes = positiveByteArray(txbytes);
	var sig = signBytes(txbytes, secretPhrase);

	signable = txbytes.slice(0, 96);
	signable = signable.concat(sig);
	signable = signable.concat(txbytes.slice(96+64));

	// now we have a full tx...
	return signable;
}

function wordBytes(word)
{
	return [(word%256), Math.floor(word/256)];
}

function bytesWord(bytes)
{
	return bytes[1]*256+bytes[0];
}

function infoModal(message)
{
	$("#modal_basic_info").modal("show");
	$("#modal_basic_info_title").text(message);
}

function reviewHandler(pin)
{
	var bytes = converters.hexStringToByteArray($("#modal_enter_pin").data("bytes"));
	$("#modal_enter_pin").removeAttr("data-bytes");
	var address = $("#accounts_account option:selected").text();
	account = findAccount(address);
	var secretPhrase = decryptSecretPhrase(account.cipher, pin, account.checksum);
	if(secretPhrase === false)
	{
		// incorrect
		infoModal("Incorrect PIN");
	}
	else
	{
		var sig = signBytes(bytes, secretPhrase);
		var signed = bytes.slice(0,96);
		signed = signed.concat(sig);
		signed = signed.concat(bytes.slice(96+64));
		$("#modal_signed_box").val(converters.byteArrayToHexString(signed));
		$("#modal_signed").modal("show");
	}
}

function verifyToken()
{
	var token = $("#modal_verify_token_token").val();
	var websiteString = $("#token_data").val();
	var resp = parseToken(token, websiteString);

	if(token.length == 160)
	{
		if(resp.isValid)
		{
			$("#modal_verify_token_group").removeClass("has-error");
			$("#modal_verify_token_group").addClass("has-success");
			$("#modal_verify_token_insert").text("(valid)");
		}
		else
		{
			$("#modal_verify_token_group").addClass("has-error");
			$("#modal_verify_token_group").removeClass("has-success");
			$("#modal_verify_token_insert").text("(invalid)");
		}
		$("#modal_verify_token_address").text(getAccountIdFromPublicKey(resp.publicKey, true));
		$("#modal_verify_token_timestamp").text(timeago(resp.timestamp));
	}
	else if(token.length == 0)
	{
		$("#modal_verify_token_group").removeClass("has-error");
		$("#modal_verify_token_group").removeClass("has-success");
		$("#modal_verify_token_insert").text("");	
		$("#modal_verify_token_address").text("N/A");
		$("#modal_verify_token_timestamp").text("N/A");
	}
	else
	{
		$("#modal_verify_token_group").addClass("has-error");
		$("#modal_verify_token_group").removeClass("has-success");
		$("#modal_verify_token_insert").text("(invalid)");	
		$("#modal_verify_token_address").text("Token Length Incorrect");
		$("#modal_verify_token_timestamp").text("N/A");
	}
}


function findAccount(address)
{
	var accounts = JSON.parse(localStorage["accounts"]);
	if(accounts && accounts.length > 0)
	{
		for(var a=0;a<accounts.length;a++)
		{
			if(accounts[a]["accountRS"] == address) return accounts[a];
		}
	}
	return false;
}

function getDetailTx(requestType, parameters, onSuccess) {
    var requestMethod;
    if (localStorage["isTestnet"] == "true") {
        requestMethod = Jay.requestMethods.single;
        Jay.singleNode = Jay.commonTestnetNodes[0];
    }
    else {
        requestMethod = Jay.requestMethods.validate;
    }
    Jay.request(requestType, parameters, onSuccess, getDetailTx_OnFail, requestMethod);
}

function getDetailTx_OnFail(resp) {
    if (resp) {
        try{
            var data = JSON.parse(resp);
            if (data.errorDescription) {
                alert(data.errorDescription + ". Please try again shortly.");
            }
            else {
                alert("Fail to get transaction details. Please try again shortly.");
            }
        }
        catch (err) {
            if (resp.error) {
                alert(resp.error + ". Please try again shortly.");
            }
            else {
                alert("Fail to get transaction details. Please try again shortly.");
            }
        }
    }
    else {
        alert("Fail to get transaction details. Please try again shortly.");
    }
}

function isGetTxDetails() {
    if (localStorage["isAlwaysSend"] == "true") {
        $("#detailtx_loading").show();
        return true;
    }
    else return false;
}

$("document").ready(function() {

	$("#modal_enter_pin").on("show.bs.modal", function(e) {
		$("#modal_enter_pin_input").val("");

		var source = $(e.relatedTarget).data("source");
		if(source === undefined) source = $("#modal_enter_pin").data("source");

		if(source == "accounts_new")
		{
			$("#modal_enter_pin_title").text("Enter PIN for New Account");
		}
		else if(source == "change")
		{
			$("#modal_enter_pin_title").text("Enter Old PIN");
		}
		else if(source == "newpin")
		{
			$("#modal_enter_pin_title").text("Enter New PIN");
		}
		else if(source =="export")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Export");
		}
		else if(source == "delete")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Delete");
		}
		else if(source == "import")
		{
			$("#modal_enter_pin_title").text("Enter PIN for New Account");
		}
		else if(source == "token")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Create Token");
		}
		else if(source == "quicksend")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Quicksend");
		}
		else if(source == "review")
		{
			$("#modal_enter_pin_title").text("Enter PIN to Sign Transaction");
		}
		$("#modal_enter_pin_accept").data("source", source);
	});

	$("#modal_enter_pin_cancel").click(function() {
		$("#modal_enter_pin_input").val("");
	});
	$("#modal_enter_pin_accept").click(function() {
		$(this).modal("hide");
		pinHandler($("#modal_enter_pin_accept").data("source"), $("#modal_enter_pin_input").val());
	})

	$(".modal_enter_pin_number").click(function() {
		$("#modal_enter_pin_input").val($("#modal_enter_pin_input").val() + $(this).data("number"));
	});
	$("#modal_enter_pin_clear").click(function() {
		$("#modal_enter_pin_input").val("");
	})
	$("#modal_enter_pin_back").click(function() {
		$("#modal_enter_pin_input").val($("#modal_enter_pin_input").val().substring(0, $("#modal_enter_pin_input").val().length-1));
	})

	$(".account_selector").change(function(e) {
		var source = $(this).data("source");
		var account = $("#"+source+"_account option:selected").text();

		$(".account_selector option").removeAttr("selected");
		$(".account_selector option:contains("+account+")").prop("selected", "selected");
	});

	$("#modal_accounts_info").on("show.bs.modal", function(e) {
		var source = $(e.relatedTarget).data("source");
		var address = $("#"+source+"_account option:selected").text();
		var account = findAccount(address);

		if(account === false)
		{
			$("#modal_accounts_info_address").val("Account Not Found");
		}
		else
		{
			$("#modal_accounts_info_address").val(account["accountRS"]);
			$("#modal_accounts_info_public_key").val(account["publicKey"]);
		}
	})

	$("#modal_backup").on("show.bs.modal", function(e) {
		if(localStorage["accounts"] && JSON.parse(localStorage["accounts"]).length != 0)
		{
			$("#modal_backup_box").val(localStorage["accounts"]);
		}
		else 
		{
			$("#modal_backup_box").val("No accounts are added.")
		}
	})

	$("#modal_accounts_new_add").click(function() {
		storeAccount(pendingAccount);
		pendingAccount = undefined;
		loadAccounts();
		$("#modal_accounts_new").modal("hide");
		infoModal("Account Successfully Added");
	});
	$("#modal_accounts_new_cancel").click(function() {
		pendingAccount = undefined;
	})

	$("#modal_delete_delete").click(function(e) {
		// actually delete now
		$("#modal_delete").modal("hide");
		var address = $("#accounts_account option:selected").text();
		var data = localStorage["accounts"];
		var accounts = JSON.parse(localStorage["accounts"]);

		for(var a=0;a<accounts.length;a++)
		{
			if(accounts[a]["accountRS"] == address)
			{
				accounts.splice(a, 1);
			}
		}
		localStorage["accounts"] = JSON.stringify(accounts);
		loadAccounts();
		infoModal("Account Deleted");
	});

	$("#modal_import_add").click(function() {
		$("#modal_import").data("import", $("#modal_import_key").val());
		$("#modal_import").modal("hide");
		$("#modal_import_key").val("");
		$("#modal_enter_pin").data("source", "import");
		$("#modal_enter_pin").modal("show");
	})

	$("#token_form").submit(function(e) {
		e.preventDefault();
		$("#modal_enter_pin").data("source", "token");
		$("#modal_enter_pin").modal("show");
	})

	$("#transact_continue").click(function() {
		startTransact();
	})
	$("#transact_form").submit(function() {
		startTransact();
	})

	$("#modal_quicksend_send").click(function() {
		$("#modal_quicksend").modal("hide");
		var amount = $("#modal_quicksend_amount").val();
		$("#modal_quicksend_amount").val("");
		var sender = $("#modal_quicksend").data("sender");
		var recipient = $("#modal_quicksend").data("recipient");
		$("#modal_enter_pin").data("source", "quicksend");
		$("#modal_enter_pin").data("amount", amount);
		$("#modal_enter_pin").data("sender", sender);
		$("#modal_enter_pin").data("recipient", recipient);
		$("#modal_enter_pin").modal("show");
	})

	$("#modal_review_continue").click(function() {
		var bytes = $("#modal_review").data("bytes");
		$("#modal_review").modal("hide");
		$("#modal_enter_pin").data("source", "review");
		$("#modal_enter_pin").data("bytes", bytes);
		$("#modal_enter_pin").modal("show");
	})

	$("#modal_signed_broadcast").click(function() {
		broadcastTransaction(getBroadcastNode(), $("#modal_signed_box").val());
	});

	$("#modal_quick_sure_send").click(function() {
	    broadcastTransaction(getBroadcastNode(), $("#modal_quick_sure").data("tx"));
	})

	$("#modal_verify_token").on("show.bs.modal", function() {
		verifyToken();
	})

	$("#modal_verify_token_token").on("input propertychange", function() {
		verifyToken();
	})

	$("#modal_broadcast").on("show.bs.modal", function() {
		var old = localStorage["node"];
		if (localStorage["isTestnet"] == "true") {
		    old += " (testnet)";
		    $("#modal_broadcast_testnet").prop('checked', true)
		}
		else {
		    old += " (mainnet)";
		    $("#modal_broadcast_testnet").prop('checked', false);
		}
		if (localStorage["isAlwaysSend"] == "true") $("#modal_broadcast_always_send").prop('checked', true);
		else $("#modal_broadcast_always_send").prop('checked', false);
		$("#modal_broadcast_old").text(old);
		$("#modal_broadcast_node").val("");
	})

	$("#modal_broadcast_save").click(function() {
		var node = $("#modal_broadcast_node").val();
		var isTestnet = $("#modal_broadcast_testnet").is(":checked");
		var isAlwaysSend = $("#modal_broadcast_always_send").is(":checked");
		setBroadcastNode(node, isTestnet, isAlwaysSend);
		$("#modal_broadcast").modal("hide");
	})

	$("#popout_tabs a").click(function (e) {
	    var tab = e.target.attributes.href.value;
	    var focus;
	    if (tab == "#transact") focus = "#transact_transaction";
	    else if (tab == "#token") focus = "#token_data";

	    if (focus) {
	        setTimeout(function () { $(focus).focus(); }, 10);
	    }
	})

	$(".modal").on("shown.bs.modal", function (e) {
	    setTimeout(function () { $("#" + e.target.id).find('input:enabled:not([readonly])').first().focus(); }, 10);
	})

	$("#transact_transaction").keypress(function (e) {
	    if (e.which == "13") {
	        e.preventDefault();
	        if ($(this).val()) {
	            $(this).submit();
	        }
	    }
	});

	Jay.nodeScan(function () { });
	if (localStorage["isTestnet"] == "true") Jay.isTestnet = true;
}) 

})();

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
