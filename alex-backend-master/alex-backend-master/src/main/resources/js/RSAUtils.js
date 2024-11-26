let dbits

const canary = 0xdeadbeefcafe

const j_lm = (canary & 0xffffff) === 0xefcafe



function BigInteger(a, b, c) {

    if (a != null)

        if ('number' === typeof a) this.fromNumber(a, b, c)

        else if (b == null && 'string' !== typeof a) this.fromString(a, 256)

        else this.fromString(a, b)

}

function nbi() {

    return new BigInteger(null)

}

function am1(i, x, w, j, c, n) {

    while (--n >= 0) {

        const v = x * this[i++] + w[j] + c

        c = Math.floor(v / 0x4000000)

        w[j++] = v & 0x3ffffff

    }

    return c

}

function am2(i, x, w, j, c, n) {

    const xl = x & 0x7fff,

        xh = x >> 15

    while (--n >= 0) {

        let l = this[i] & 0x7fff

        const h = this[i++] >> 15

        const m = xh * l + h * xl

        l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff)

        c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30)

        w[j++] = l & 0x3fffffff

    }

    return c

}

function am3(i, x, w, j, c, n) {

    const xl = x & 0x3fff,

        xh = x >> 14

    while (--n >= 0) {

        let l = this[i] & 0x3fff

        const h = this[i++] >> 14

        const m = xh * l + h * xl

        l = xl * l + ((m & 0x3fff) << 14) + w[j] + c

        c = (l >> 28) + (m >> 14) + xh * h

        w[j++] = l & 0xfffffff

    }

    return c

}



BigInteger.prototype.am = am3

dbits = 28



BigInteger.prototype.DB = dbits

BigInteger.prototype.DM = (1 << dbits) - 1

BigInteger.prototype.DV = 1 << dbits

const BI_FP = 52

BigInteger.prototype.FV = Math.pow(2, BI_FP)

BigInteger.prototype.F1 = BI_FP - dbits

BigInteger.prototype.F2 = 2 * dbits - BI_FP

const BI_RM = '0123456789abcdefghijklmnopqrstuvwxyz'

const BI_RC = []

let rr, vv

rr = '0'.charCodeAt(0)

for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv

rr = 'a'.charCodeAt(0)

for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv

rr = 'A'.charCodeAt(0)

for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv

function int2char(n) {

    return BI_RM.charAt(n)

}

function intAt(s, i) {

    const c = BI_RC[s.charCodeAt(i)]

    return c == null ? -1 : c

}

function bnpCopyTo(r) {

    for (let i = this.t - 1; i >= 0; --i) r[i] = this[i]

    r.t = this.t

    r.s = this.s

}

function bnpFromInt(x) {

    this.t = 1

    this.s = x < 0 ? -1 : 0

    if (x > 0) this[0] = x

    else if (x < -1) this[0] = x + this.DV

    else this.t = 0

}

function nbv(i) {

    const r = nbi()

    r.fromInt(i)

    return r

}

function bnpFromString(s, b) {

    let k

    if (b == 16) k = 4

    else if (b == 8) k = 3

    else if (b == 256) k = 8

    else if (b == 2) k = 1

    else if (b == 32) k = 5

    else if (b == 4) k = 2

    else {

        this.fromRadix(s, b)

        return

    }

    this.t = 0

    this.s = 0

    let i = s.length,

        mi = false,

        sh = 0

    while (--i  >= 0) {

        const x = k == 8 ? s[i] & 0xff : intAt(s, i)

        if (x < 0) {

            if (s.charAt(i) == '-') mi = true

            continue

        }

        mi = false

        if (sh == 0) this[this.t++] = x

        else if (sh + k > this.DB) {

            this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh

            this[this.t++] = x >> (this.DB - sh)

        } else this[this.t - 1] |= x << sh

        sh += k

        if (sh >= this.DB) sh -= this.DB

    }

    if (k == 8 && (s[0] & 0x80) != 0) {

        this.s = -1

        if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh

    }

    this.clamp()

    if (mi) BigInteger.ZERO.subTo(this, this)

}

function bnpClamp() {

    const c = this.s & this.DM

    while (this.t > 0 && this[this.t - 1] == c) --this.t

}

function bnToString(b) {

    if (this.s < 0) return '-' + this.negate().toString(b)

    let k

    if (b == 16) k = 4

    else if (b == 8) k = 3

    else if (b == 2) k = 1

    else if (b == 32) k = 5

    else if (b == 4) k = 2

    else return this.toRadix(b)

    const km = (1 << k) - 1

    let d,

        m = false,

        r = '',

        i = this.t

    let p = this.DB - ((i * this.DB) % k)

    if (i-- > 0) {

        if (p < this.DB && (d = this[i] >> p) > 0) {

            m = true

            r = int2char(d)

        }

        while (i >= 0) {

            if (p < k) {

                d = (this[i] & ((1 << p) - 1)) << (k - p)

                d |= this[--i] >> (p += this.DB - k)

            } else {

                d = (this[i] >> (p -= k)) & km

                if (p <= 0) {

                    p += this.DB

                    --i

                }

            }

            if (d > 0) m = true

            if (m) r += int2char(d)

        }

    }

    return m ? r : '0'

}

function bnNegate() {

    const r = nbi()

    BigInteger.ZERO.subTo(this, r)

    return r

}

function bnAbs() {

    return this.s < 0 ? this.negate() : this

}

function bnCompareTo(a) {

    let r = this.s - a.s

    if (r != 0) return r

    let i = this.t

    r = i - a.t

    if (r != 0) return r

    while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r

    return 0

}

function nbits(x) {

    let r = 1,

        t

    if ((t = x >>> 16) != 0) {

        x = t

        r += 16

    }

    if ((t = x >> 8) != 0) {

        x = t

        r += 8

    }

    if ((t = x >> 4) != 0) {

        x = t

        r += 4

    }

    if ((t = x >> 2) != 0) {

        x = t

        r += 2

    }

    if ((t = x >> 1) != 0) {

        x = t

        r += 1

    }

    return r

}

function bnBitLength() {

    if (this.t <= 0) return 0

    return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM))

}

function bnpDLShiftTo(n, r) {

    let i

    for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i]

    for (i = n - 1; i >= 0; --i) r[i] = 0

    r.t = this.t + n

    r.s = this.s

}

function bnpDRShiftTo(n, r) {

    for (let i = n; i < this.t; ++i) r[i - n] = this[i]

    r.t = Math.max(this.t - n, 0)

    r.s = this.s

}

function bnpLShiftTo(n, r) {

    const bs = n % this.DB

    const cbs = this.DB - bs

    const bm = (1 << cbs) - 1

    const ds = Math.floor(n / this.DB)

    let c = (this.s << bs) & this.DM,

        i

    for (i = this.t - 1; i >= 0; --i) {

        r[i + ds + 1] = (this[i] >> cbs) | c

        c = (this[i] & bm) << bs

    }

    for (i = ds - 1; i >= 0; --i) r[i] = 0

    r[ds] = c

    r.t = this.t + ds + 1

    r.s = this.s

    r.clamp()

}

function bnpRShiftTo(n, r) {

    r.s = this.s

    const ds = Math.floor(n / this.DB)

    if (ds >= this.t) {

        r.t = 0

        return

    }

    const bs = n % this.DB

    const cbs = this.DB - bs

    const bm = (1 << bs) - 1

    r[0] = this[ds] >> bs

    for (let i = ds + 1; i < this.t; ++i) {

        r[i - ds - 1] |= (this[i] & bm) << cbs

        r[i - ds] = this[i] >> bs

    }

    if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs

    r.t = this.t - ds

    r.clamp()

}

function bnpSubTo(a, r) {

    let i = 0,

        c = 0

    const m = Math.min(a.t, this.t)

    while (i < m) {

        c += this[i] - a[i]

        r[i++] = c & this.DM

        c >>= this.DB

    }

    if (a.t < this.t) {

        c -= a.s

        while (i < this.t) {

            c += this[i]

            r[i++] = c & this.DM

            c >>= this.DB

        }

        c += this.s

    } else {

        c += this.s

        while (i < a.t) {

            c -= a[i]

            r[i++] = c & this.DM

            c >>= this.DB

        }

        c -= a.s

    }

    r.s = c < 0 ? -1 : 0

    if (c < -1) r[i++] = this.DV + c

    else if (c > 0) r[i++] = c

    r.t = i

    r.clamp()

}

function bnpMultiplyTo(a, r) {

    const x = this.abs(),

        y = a.abs()

    let i = x.t

    r.t = i + y.t

    while (--i >= 0) r[i] = 0

    for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t)

    r.s = 0

    r.clamp()

    if (this.s != a.s) BigInteger.ZERO.subTo(r, r)

}

function bnpSquareTo(r) {

    const x = this.abs()

    let i = (r.t = 2 * x.t)

    while (--i >= 0) r[i] = 0

    for (i = 0; i < x.t - 1; ++i) {

        const c = x.am(i, x[i], r, 2 * i, 0, 1)

        if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {

            r[i + x.t] -= x.DV

            r[i + x.t + 1] = 1

        }

    }

    if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1)

    r.s = 0

    r.clamp()

}

function bnpDivRemTo(m, q, r) {

    const pm = m.abs()

    if (pm.t <= 0) return

    const pt = this.abs()

    if (pt.t < pm.t) {

        if (q != null) q.fromInt(0)

        if (r != null) this.copyTo(r)

        return

    }

    if (r == null) r = nbi()

    const y = nbi(),

        ts = this.s,

        ms = m.s

    const nsh = this.DB - nbits(pm[pm.t - 1])

    if (nsh > 0) {

        pm.lShiftTo(nsh, y)

        pt.lShiftTo(nsh, r)

    } else {

        pm.copyTo(y)

        pt.copyTo(r)

    }

    const ys = y.t

    const y0 = y[ys - 1]

    if (y0 == 0) return

    const yt = y0 * (1 << this.F1) + (ys > 1 ? y[ys - 2] >> this.F2 : 0)

    const d1 = this.FV / yt,

        d2 = (1 << this.F1) / yt,

        e = 1 << this.F2

    let i = r.t,

        j = i - ys



    const t = q == null ? nbi() : q

    y.dlShiftTo(j, t)

    if (r.compareTo(t) >= 0) {

        r[r.t++] = 1

        r.subTo(t, r)

    }

    BigInteger.ONE.dlShiftTo(ys, t)

    t.subTo(y, y)

    while (y.t < ys) y[y.t++] = 0

    while (--j >= 0) {

        let qd = r[--i] == y0 ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2)

        if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {

            y.dlShiftTo(j, t)

            r.subTo(t, r)

            while (r[i] < --qd) r.subTo(t, r)

        }

    }

    if (q != null) {

        r.drShiftTo(ys, q)

        if (ts != ms) BigInteger.ZERO.subTo(q, q)

    }

    r.t = ys

    r.clamp()

    if (nsh > 0) r.rShiftTo(nsh, r)

    if (ts < 0) BigInteger.ZERO.subTo(r, r)

}

function bnMod(a) {

    const r = nbi()

    this.abs().divRemTo(a, null, r)

    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r)

    return r

}

function Classic(m) {

    this.m = m

}

function cConvert(x) {

    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m)

    return x

}

function cRevert(x) {

    return x

}

function cReduce(x) {

    x.divRemTo(this.m, null, x)

}

function cMulTo(x, y, r) {

    x.multiplyTo(y, r)

    this.reduce(r)

}

function cSqrTo(x, r) {

    x.squareTo(r)

    this.reduce(r)

}

Classic.prototype.convert = cConvert

Classic.prototype.revert = cRevert

Classic.prototype.reduce = cReduce

Classic.prototype.mulTo = cMulTo

Classic.prototype.sqrTo = cSqrTo

function bnpInvDigit() {

    if (this.t < 1) return 0

    const x = this[0]

    if ((x & 1) == 0) return 0

    let y = x & 3

    y = (y * (2 - (x & 0xf) * y)) & 0xf

    y = (y * (2 - (x & 0xff) * y)) & 0xff

    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff

    y = (y * (2 - ((x * y) % this.DV))) % this.DV

    return y > 0 ? this.DV - y : -y

}

function Montgomery(m) {

    this.m = m

    this.mp = m.invDigit()

    this.mpl = this.mp & 0x7fff

    this.mph = this.mp >> 15

    this.um = (1 << (m.DB - 15)) - 1

    this.mt2 = 2 * m.t

}

function montConvert(x) {

    const r = nbi()

    x.abs().dlShiftTo(this.m.t, r)

    r.divRemTo(this.m, null, r)

    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r)

    return r

}

function montRevert(x) {

    const r = nbi()

    x.copyTo(r)

    this.reduce(r)

    return r

}

function montReduce(x) {

    while (x.t <= this.mt2) x[x.t++] = 0

    for (let i = 0; i < this.m.t; ++i) {

        let j = x[i] & 0x7fff

        const u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM

        j = i + this.m.t

        x[j] += this.m.am(0, u0, x, i, 0, this.m.t)

        while (x[j] >= x.DV) {

            x[j] -= x.DV

            x[++j]++

        }

    }

    x.clamp()

    x.drShiftTo(this.m.t, x)

    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x)

}

function montSqrTo(x, r) {

    x.squareTo(r)

    this.reduce(r)

}

function montMulTo(x, y, r) {

    x.multiplyTo(y, r)

    this.reduce(r)

}

Montgomery.prototype.convert = montConvert

Montgomery.prototype.revert = montRevert

Montgomery.prototype.reduce = montReduce

Montgomery.prototype.mulTo = montMulTo

Montgomery.prototype.sqrTo = montSqrTo

function bnpIsEven() {

    return (this.t > 0 ? this[0] & 1 : this.s) == 0

}

function bnpExp(e, z) {

    if (e > 0xffffffff || e < 1) return BigInteger.ONE

    let r = nbi(),

        r2 = nbi(),

        i = nbits(e) - 1

    const g = z.convert(this)

    g.copyTo(r)

    while (--i >= 0) {

        z.sqrTo(r, r2)

        if ((e & (1 << i)) > 0) z.mulTo(r2, g, r)

        else {

            const t = r

            r = r2

            r2 = t

        }

    }

    return z.revert(r)

}

function bnModPowInt(e, m) {

    let z

    if (e < 256 || m.isEven()) z = new Classic(m)

    else z = new Montgomery(m)

    return this.exp(e, z)

}

BigInteger.prototype.copyTo = bnpCopyTo

BigInteger.prototype.fromInt = bnpFromInt

BigInteger.prototype.fromString = bnpFromString

BigInteger.prototype.clamp = bnpClamp

BigInteger.prototype.dlShiftTo = bnpDLShiftTo

BigInteger.prototype.drShiftTo = bnpDRShiftTo

BigInteger.prototype.lShiftTo = bnpLShiftTo

BigInteger.prototype.rShiftTo = bnpRShiftTo

BigInteger.prototype.subTo = bnpSubTo

BigInteger.prototype.multiplyTo = bnpMultiplyTo

BigInteger.prototype.squareTo = bnpSquareTo

BigInteger.prototype.divRemTo = bnpDivRemTo

BigInteger.prototype.invDigit = bnpInvDigit

BigInteger.prototype.isEven = bnpIsEven

BigInteger.prototype.exp = bnpExp

BigInteger.prototype.toString = bnToString

BigInteger.prototype.negate = bnNegate

BigInteger.prototype.abs = bnAbs

BigInteger.prototype.compareTo = bnCompareTo

BigInteger.prototype.bitLength = bnBitLength

BigInteger.prototype.mod = bnMod

BigInteger.prototype.modPowInt = bnModPowInt

BigInteger.ZERO = nbv(0)

BigInteger.ONE = nbv(1)

function Arcfour() {

    this.i = 0

    this.j = 0

    this.S = []

}

function ARC4init(key) {

    let i, j, t

    for (i = 0; i < 256; ++i) this.S[i] = i

    j = 0

    for (i = 0; i < 256; ++i) {

        j = (j + this.S[i] + key[i % key.length]) & 255

        t = this.S[i]

        this.S[i] = this.S[j]

        this.S[j] = t

    }

    this.i = 0

    this.j = 0

}

function ARC4next() {

    this.i = (this.i + 1) & 255

    this.j = (this.j + this.S[this.i]) & 255

    const t = this.S[this.i]

    this.S[this.i] = this.S[this.j]

    this.S[this.j] = t

    return this.S[(t + this.S[this.i]) & 255]

}

Arcfour.prototype.init = ARC4init

Arcfour.prototype.next = ARC4next

function prng_newstate() {

    return new Arcfour()

}

const rng_psize = 256

let rng_state

let rng_pool

let rng_pptr

function rng_seed_int(x) {

    rng_pool[rng_pptr++] ^= x & 255

    rng_pool[rng_pptr++] ^= (x >> 8) & 255

    rng_pool[rng_pptr++] ^= (x >> 16) & 255

    rng_pool[rng_pptr++] ^= (x >> 24) & 255

    if (rng_pptr >= rng_psize) rng_pptr -= rng_psize

}

function rng_seed_time() {

    rng_seed_int(new Date().getTime())

}

if (rng_pool == null) {

    rng_pool = []

    rng_pptr = 0

    let t



    while (rng_pptr < rng_psize) {

        t = Math.floor(65536 * Math.random())

        rng_pool[rng_pptr++] = t >>> 8

        rng_pool[rng_pptr++] = t & 255

    }

    rng_pptr = 0

    rng_seed_time()

}

function rng_get_byte() {

    if (rng_state == null) {

        rng_seed_time()

        rng_state = prng_newstate()

        rng_state.init(rng_pool)

        for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr) rng_pool[rng_pptr] = 0

        rng_pptr = 0

    }

    return rng_state.next()

}

function rng_get_bytes(ba) {

    let i

    for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte()

}

function SecureRandom() {}

SecureRandom.prototype.nextBytes = rng_get_bytes

function parseBigInt(str, r) {

    return new BigInteger(str, r)

}

function linebrk(s, n) {

    let ret = ''

    let i = 0

    while (i + n < s.length) {

        ret += s.substring(i, i + n) + '\n'

        i += n

    }

    return ret + s.substring(i, s.length)

}

function byte2Hex(b) {

    if (b < 0x10) return '0' + b.toString(16)

    return b.toString(16)

}

function pkcs1pad2(s, n) {

    //2位长度+pin+rnd

    if (n < s.length + 2) {

        //alert("密码太长!");

        return null

    }

    const ba = []

    let i = s.length - 1

    const len = s.length

    if (len < 100) {

        ba[0] = 0x30 + len / 10

        ba[1] = 0x30 + (len % 10)

    } else {

        //alert("密码太长!");

        return null

    }

    let j = 2

    i = 0

    while (i < len && n > 0) {

        ba[j++] = s.charCodeAt(i++)

    }

    const rng = new SecureRandom()

    const x = []

    while (j < n) {

        x[0] = 0

        while (x[0] == 0) rng.nextBytes(x)

        ba[j++] = x[0]

    }

    return new BigInteger(ba)

}

function RSAKey() {

    this.n = null

    this.e = 0

    this.d = null

    this.p = null

    this.q = null

    this.dmp1 = null

    this.dmq1 = null

    this.coeff = null

}

function RSASetPublic(N, E) {

    if (N != null && E != null && N.length > 0 && E.length > 0) {

        this.n = parseBigInt(N, 16)

        this.e = parseInt(E, 16)

    }

}

function RSADoPublic(x) {

    return x.modPowInt(this.e, this.n)

}

function RSAEncrypt(text, type) {

    const m = pkcs1pad2(text, (this.n.bitLength() + 7) >> 3)

    if (m == null) return null

    const c = this.doPublic(m)

    if (c == null) return null

    let h = c.toString(16).toUpperCase()

    //根据密钥长度补0

    const gapLen = (type === 'login' ? 256 : 512) - h.length

    for (let i = 0; i < gapLen; i = i + 1) {

        h = '0' + h

    }

    return h

}

RSAKey.prototype.doPublic = RSADoPublic

RSAKey.prototype.setPublic = RSASetPublic

RSAKey.prototype.encrypt = RSAEncrypt

class RSAUtils {

    static rsaBdg(str, type, key) {

        // // 交易密码加密公钥（生产环境）

        // let key = 'C4FEAA0639647A9854C58DD70BAB6B13C49307104DEB9B963896FC40EDA94AE6842FD61EC4D969FD66FD6633339D2BB1C99F5FFB559828454C510AE16040B6016EEED3F253EEC13058F2BEA5C705ADED9C6AAB39A5CC58F76ACA6D87E2FE559FA15A0ED345B489B2F9D2E140C71DDCB8901D56A6441014FDB09C9A96DE2914C6B98EA0A9E28AFB60E2F4658AB92882DE68CAE4943B7D77B9DF69064E4B6F1379623101E34BBCD7E05AC59E70AC3C1F5EA9735C3E42A9919F53C9BA3CD9F30BC7543C21C687B8AC2834E7A760722237B11375BA92F701FF50FB7EA53706166158EDFD3E77423DB2AE5138653DE7D359E3BF033FA48273697FCD895A50CDEC43AB';

        // // 交易密码加密公钥（测试环境 // console.log('key from env:',AppConst.luIntlH5Env) // if (AppConst.luIntlH5Env === 'development') {

        // console.log('key dev:')

        // key = 'AD5F78EC0E80ED611522F4386CC1578A7D1C3EADF90036B941D176C92EAFDC89A74CAD4C92B3C6A88C84C3F6FAE1AFDB9DA8B52B858129F819E45355FAC72C285FF3438598DEC924A72964FDE65A2966856B8EA55053BA3A663B7CC5FA3841B36DE428D19599157634FEF3F852F7231C2F5D61F2E0045A6903AD003E400A32F9C50CABBFFE9421879236AEC2EC385A59B6E5DA59EBE965EC32A5452014F2D635A0CFBD8669FA4BB67CD38DEDEB67E911D8512DDF135B325D13ABDBF3B058DDF585F6EE4476BE0D6958098A17C108B5017FB41E7CADC6546890ACCA298ADDCC06C63B2AFB8241A1A31DA275A9D6A3A19B004217611652716718C8B0150B00B427'; // }

        // // 登录密码加密公钥（不区分生产和测试环境）

        // if (type === 'login') { // key = 'BE24E372DC1B329633A6A014A7C02797915E3C363DD6EE119377BD645329B7E6446B4A71AC5F878EBC870C6D8BFD3C06B92E6C6E93390B34192A7A9E430800091761473FAC2CC0A68A828B2589A8CB729C19161E8E27F4C0F3CDE9701FAFE48D2B65947799072AFA6A3F2D7BDBEF8B6D7429C2D115A3E5F723467D57B3AC6967'; // }

        const RSA = new RSAKey()

        RSA.setPublic(key, type === 'login' ? '10001' : '3')

        const res = RSA.encrypt(str, type)

        return res

    }

}

var passwd = RSAUtils.rsaBdg("qwert666", "login", "be24e372dc1b329633a6a014a7c02797915e3c363dd6ee119377bd645329b7e6446b4a71ac5f878ebc870c6d8bfd3c06b92e6c6e93390b34192a7a9e430800091761473fac2cc0a68a828b2589a8cb729c19161e8e27f4c0f3cde9701fafe48d2b65947799072afa6a3f2d7bdbef8b6d7429c2d115a3e5f723467d57b3ac6967")

console.log("passwd=",passwd)
