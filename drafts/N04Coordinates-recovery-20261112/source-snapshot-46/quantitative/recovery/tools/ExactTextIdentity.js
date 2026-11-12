function utf8Bytes(text) {
  const bytes = unescape(encodeURIComponent(text));
  return Array.from(bytes, c => c.charCodeAt(0));
}
function paddedWords(text) {
  const bytes = utf8Bytes(text), bits = bytes.length * 8;
  bytes.push(128);
  while (bytes.length % 64 !== 56) bytes.push(0);
  const high = Math.floor(bits / 4294967296), low = bits >>> 0;
  for (let k = 3; k >= 0; --k) bytes.push((high >>> (8 * k)) & 255);
  for (let k = 3; k >= 0; --k) bytes.push((low >>> (8 * k)) & 255);
  const words = [];
  for (let i = 0; i < bytes.length; i += 4)
    words.push(((bytes[i] << 24) | (bytes[i+1] << 16) | (bytes[i+2] << 8) | bytes[i+3]) >>> 0);
  return words;
}
function hexWords(words) {
  return words.map(x => (x >>> 0).toString(16).padStart(8, "0")).join("");
}
function sha256(text) {
  const K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
  const H = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const data = paddedWords(text), rotr=(x,n)=>(x>>>n)|(x<<(32-n));
  for (let offset=0;offset<data.length;offset+=16) {
    const W=data.slice(offset,offset+16);
    for(let t=16;t<64;++t) {
      const x=W[t-15],y=W[t-2];
      W[t]=(W[t-16]+(rotr(x,7)^rotr(x,18)^(x>>>3))+W[t-7]+(rotr(y,17)^rotr(y,19)^(y>>>10)))>>>0;
    }
    let [a,b,c,d,e,f,g,h]=H;
    for(let t=0;t<64;++t) {
      const t1=(h+(rotr(e,6)^rotr(e,11)^rotr(e,25))+((e&f)^(~e&g))+K[t]+W[t])>>>0;
      const t2=((rotr(a,2)^rotr(a,13)^rotr(a,22))+((a&b)^(a&c)^(b&c)))>>>0;
      h=g;g=f;f=e;e=(d+t1)>>>0;d=c;c=b;b=a;a=(t1+t2)>>>0;
    }
    const S=[a,b,c,d,e,f,g,h];for(let k=0;k<8;++k)H[k]=(H[k]+S[k])>>>0;
  }
  return hexWords(H);
}
function sha1(text) {
  const H=[0x67452301,0xefcdab89,0x98badcfe,0x10325476,0xc3d2e1f0];
  const data=paddedWords(text),rotl=(x,n)=>(x<<n)|(x>>>(32-n));
  for(let offset=0;offset<data.length;offset+=16) {
    const W=data.slice(offset,offset+16);
    for(let t=16;t<80;++t)W[t]=rotl(W[t-3]^W[t-8]^W[t-14]^W[t-16],1)>>>0;
    let [a,b,c,d,e]=H;
    for(let t=0;t<80;++t) {
      const f=t<20?(b&c)|(~b&d):t<40?b^c^d:t<60?(b&c)|(b&d)|(c&d):b^c^d;
      const k=t<20?0x5a827999:t<40?0x6ed9eba1:t<60?0x8f1bbcdc:0xca62c1d6;
      const temp=(rotl(a,5)+f+e+k+W[t])>>>0;e=d;d=c;c=rotl(b,30)>>>0;b=a;a=temp;
    }
    const S=[a,b,c,d,e];for(let k=0;k<5;++k)H[k]=(H[k]+S[k])>>>0;
  }
  return hexWords(H);
}
function gitBlob(text) {
  return sha1("blob "+utf8Bytes(text).length+"\0"+text);
}
