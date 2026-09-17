import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step40809 (p25 p2026 : Prop)
    (h27 : p25)
    (h2186 : (¬ p25) ∨ (¬ p2026))
    : (¬ p2026) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2026 := Classical.byContradiction (fun h => hn h);
    let u1 : p25 := h27;
    (Or.elim h2186 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40810 (p2026 p2027 : Prop)
    (h40809 : (¬ p2026))
    (h2188 : p2026 ∨ (¬ p2027))
    : (¬ p2027) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2027 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2026) := h40809;
    (Or.elim h2188 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40811 (p1922 p2028 : Prop)
    (h2082 : p1922)
    (h2190 : (¬ p1922) ∨ (¬ p2028))
    : (¬ p2028) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2028 := Classical.byContradiction (fun h => hn h);
    let u1 : p1922 := h2082;
    (Or.elim h2190 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40812 (p1923 p2029 : Prop)
    (h2083 : p1923)
    (h2192 : (¬ p1923) ∨ (¬ p2029))
    : (¬ p2029) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2029 := Classical.byContradiction (fun h => hn h);
    let u1 : p1923 := h2083;
    (Or.elim h2192 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40813 (p1924 p2030 : Prop)
    (h2084 : p1924)
    (h2194 : (¬ p1924) ∨ (¬ p2030))
    : (¬ p2030) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2030 := Classical.byContradiction (fun h => hn h);
    let u1 : p1924 := h2084;
    (Or.elim h2194 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40814 (p1925 p2031 : Prop)
    (h2085 : p1925)
    (h2196 : (¬ p1925) ∨ (¬ p2031))
    : (¬ p2031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2031 := Classical.byContradiction (fun h => hn h);
    let u1 : p1925 := h2085;
    (Or.elim h2196 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40815 (p1926 p2032 : Prop)
    (h2086 : p1926)
    (h2198 : (¬ p1926) ∨ (¬ p2032))
    : (¬ p2032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2032 := Classical.byContradiction (fun h => hn h);
    let u1 : p1926 := h2086;
    (Or.elim h2198 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40816 (p1927 p2033 : Prop)
    (h2087 : p1927)
    (h2200 : (¬ p1927) ∨ (¬ p2033))
    : (¬ p2033) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2033 := Classical.byContradiction (fun h => hn h);
    let u1 : p1927 := h2087;
    (Or.elim h2200 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40817 (p1928 p2034 : Prop)
    (h2088 : p1928)
    (h2202 : (¬ p1928) ∨ (¬ p2034))
    : (¬ p2034) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2034 := Classical.byContradiction (fun h => hn h);
    let u1 : p1928 := h2088;
    (Or.elim h2202 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40818 (p1929 p2035 : Prop)
    (h2089 : p1929)
    (h2204 : (¬ p1929) ∨ (¬ p2035))
    : (¬ p2035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2035 := Classical.byContradiction (fun h => hn h);
    let u1 : p1929 := h2089;
    (Or.elim h2204 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40819 (p1930 p2036 : Prop)
    (h2090 : p1930)
    (h2206 : (¬ p1930) ∨ (¬ p2036))
    : (¬ p2036) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2036 := Classical.byContradiction (fun h => hn h);
    let u1 : p1930 := h2090;
    (Or.elim h2206 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40820 (p1931 p2037 : Prop)
    (h2091 : p1931)
    (h2208 : (¬ p1931) ∨ (¬ p2037))
    : (¬ p2037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2037 := Classical.byContradiction (fun h => hn h);
    let u1 : p1931 := h2091;
    (Or.elim h2208 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40821 (p1932 p2038 : Prop)
    (h2092 : p1932)
    (h2210 : (¬ p1932) ∨ (¬ p2038))
    : (¬ p2038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2038 := Classical.byContradiction (fun h => hn h);
    let u1 : p1932 := h2092;
    (Or.elim h2210 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40822 (p1933 p2039 : Prop)
    (h2093 : p1933)
    (h2212 : (¬ p1933) ∨ (¬ p2039))
    : (¬ p2039) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2039 := Classical.byContradiction (fun h => hn h);
    let u1 : p1933 := h2093;
    (Or.elim h2212 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40823 (p1934 p2040 : Prop)
    (h2094 : p1934)
    (h2214 : (¬ p1934) ∨ (¬ p2040))
    : (¬ p2040) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2040 := Classical.byContradiction (fun h => hn h);
    let u1 : p1934 := h2094;
    (Or.elim h2214 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40824 (p1935 p2041 : Prop)
    (h2095 : p1935)
    (h2216 : (¬ p1935) ∨ (¬ p2041))
    : (¬ p2041) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2041 := Classical.byContradiction (fun h => hn h);
    let u1 : p1935 := h2095;
    (Or.elim h2216 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40825 (p1936 p2042 : Prop)
    (h2096 : p1936)
    (h2218 : (¬ p1936) ∨ (¬ p2042))
    : (¬ p2042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2042 := Classical.byContradiction (fun h => hn h);
    let u1 : p1936 := h2096;
    (Or.elim h2218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40826 (p1937 p2043 : Prop)
    (h2097 : p1937)
    (h2220 : (¬ p1937) ∨ (¬ p2043))
    : (¬ p2043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2043 := Classical.byContradiction (fun h => hn h);
    let u1 : p1937 := h2097;
    (Or.elim h2220 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40827 (p1938 p2044 : Prop)
    (h2098 : p1938)
    (h2222 : (¬ p1938) ∨ (¬ p2044))
    : (¬ p2044) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2044 := Classical.byContradiction (fun h => hn h);
    let u1 : p1938 := h2098;
    (Or.elim h2222 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40828 (p1939 p2045 : Prop)
    (h2099 : p1939)
    (h2224 : (¬ p1939) ∨ (¬ p2045))
    : (¬ p2045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2045 := Classical.byContradiction (fun h => hn h);
    let u1 : p1939 := h2099;
    (Or.elim h2224 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40829 (p1940 p2046 : Prop)
    (h2100 : p1940)
    (h2226 : (¬ p1940) ∨ (¬ p2046))
    : (¬ p2046) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2046 := Classical.byContradiction (fun h => hn h);
    let u1 : p1940 := h2100;
    (Or.elim h2226 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40830 (p1941 p2047 : Prop)
    (h2101 : p1941)
    (h2228 : (¬ p1941) ∨ (¬ p2047))
    : (¬ p2047) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2047 := Classical.byContradiction (fun h => hn h);
    let u1 : p1941 := h2101;
    (Or.elim h2228 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40831 (p1942 p2048 : Prop)
    (h2102 : p1942)
    (h2230 : (¬ p1942) ∨ (¬ p2048))
    : (¬ p2048) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2048 := Classical.byContradiction (fun h => hn h);
    let u1 : p1942 := h2102;
    (Or.elim h2230 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40832 (p1943 p2049 : Prop)
    (h2103 : p1943)
    (h2232 : (¬ p1943) ∨ (¬ p2049))
    : (¬ p2049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2049 := Classical.byContradiction (fun h => hn h);
    let u1 : p1943 := h2103;
    (Or.elim h2232 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40833 (p1944 p2050 : Prop)
    (h2104 : p1944)
    (h2234 : (¬ p1944) ∨ (¬ p2050))
    : (¬ p2050) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2050 := Classical.byContradiction (fun h => hn h);
    let u1 : p1944 := h2104;
    (Or.elim h2234 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40834 (p1945 p2051 : Prop)
    (h2105 : p1945)
    (h2236 : (¬ p1945) ∨ (¬ p2051))
    : (¬ p2051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2051 := Classical.byContradiction (fun h => hn h);
    let u1 : p1945 := h2105;
    (Or.elim h2236 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40835 (p1946 p2052 : Prop)
    (h2106 : p1946)
    (h2238 : (¬ p1946) ∨ (¬ p2052))
    : (¬ p2052) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2052 := Classical.byContradiction (fun h => hn h);
    let u1 : p1946 := h2106;
    (Or.elim h2238 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40836 (p1947 p2053 : Prop)
    (h2107 : p1947)
    (h2240 : (¬ p1947) ∨ (¬ p2053))
    : (¬ p2053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2053 := Classical.byContradiction (fun h => hn h);
    let u1 : p1947 := h2107;
    (Or.elim h2240 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40837 (p1948 p2054 : Prop)
    (h2108 : p1948)
    (h2242 : (¬ p1948) ∨ (¬ p2054))
    : (¬ p2054) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2054 := Classical.byContradiction (fun h => hn h);
    let u1 : p1948 := h2108;
    (Or.elim h2242 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40838 (p1949 p2055 : Prop)
    (h2109 : p1949)
    (h2244 : (¬ p1949) ∨ (¬ p2055))
    : (¬ p2055) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2055 := Classical.byContradiction (fun h => hn h);
    let u1 : p1949 := h2109;
    (Or.elim h2244 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40839 (p1950 p2056 : Prop)
    (h2110 : p1950)
    (h2246 : (¬ p1950) ∨ (¬ p2056))
    : (¬ p2056) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2056 := Classical.byContradiction (fun h => hn h);
    let u1 : p1950 := h2110;
    (Or.elim h2246 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40840 (p1951 p2057 : Prop)
    (h2111 : p1951)
    (h2248 : (¬ p1951) ∨ (¬ p2057))
    : (¬ p2057) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2057 := Classical.byContradiction (fun h => hn h);
    let u1 : p1951 := h2111;
    (Or.elim h2248 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40841 (p1952 p2058 : Prop)
    (h2112 : p1952)
    (h2250 : (¬ p1952) ∨ (¬ p2058))
    : (¬ p2058) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2058 := Classical.byContradiction (fun h => hn h);
    let u1 : p1952 := h2112;
    (Or.elim h2250 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40842 (p1953 p2059 : Prop)
    (h2113 : p1953)
    (h2252 : (¬ p1953) ∨ (¬ p2059))
    : (¬ p2059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2059 := Classical.byContradiction (fun h => hn h);
    let u1 : p1953 := h2113;
    (Or.elim h2252 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40843 (p1954 p2060 : Prop)
    (h2114 : p1954)
    (h2254 : (¬ p1954) ∨ (¬ p2060))
    : (¬ p2060) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2060 := Classical.byContradiction (fun h => hn h);
    let u1 : p1954 := h2114;
    (Or.elim h2254 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40844 (p1955 p2061 : Prop)
    (h2115 : p1955)
    (h2256 : (¬ p1955) ∨ (¬ p2061))
    : (¬ p2061) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2061 := Classical.byContradiction (fun h => hn h);
    let u1 : p1955 := h2115;
    (Or.elim h2256 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40845 (p1956 p2062 : Prop)
    (h2116 : p1956)
    (h2258 : (¬ p1956) ∨ (¬ p2062))
    : (¬ p2062) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2062 := Classical.byContradiction (fun h => hn h);
    let u1 : p1956 := h2116;
    (Or.elim h2258 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40846 (p1957 p2063 : Prop)
    (h2117 : p1957)
    (h2260 : (¬ p1957) ∨ (¬ p2063))
    : (¬ p2063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2063 := Classical.byContradiction (fun h => hn h);
    let u1 : p1957 := h2117;
    (Or.elim h2260 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40847 (p1958 p2064 : Prop)
    (h2118 : p1958)
    (h2262 : (¬ p1958) ∨ (¬ p2064))
    : (¬ p2064) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2064 := Classical.byContradiction (fun h => hn h);
    let u1 : p1958 := h2118;
    (Or.elim h2262 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40848 (p1959 p2065 : Prop)
    (h2119 : p1959)
    (h2264 : (¬ p1959) ∨ (¬ p2065))
    : (¬ p2065) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2065 := Classical.byContradiction (fun h => hn h);
    let u1 : p1959 := h2119;
    (Or.elim h2264 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40849 (p1960 p2066 : Prop)
    (h2120 : p1960)
    (h2266 : (¬ p1960) ∨ (¬ p2066))
    : (¬ p2066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2066 := Classical.byContradiction (fun h => hn h);
    let u1 : p1960 := h2120;
    (Or.elim h2266 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40850 (p1961 p2067 : Prop)
    (h2121 : p1961)
    (h2268 : (¬ p1961) ∨ (¬ p2067))
    : (¬ p2067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2067 := Classical.byContradiction (fun h => hn h);
    let u1 : p1961 := h2121;
    (Or.elim h2268 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40851 (p1962 p2068 : Prop)
    (h2122 : p1962)
    (h2270 : (¬ p1962) ∨ (¬ p2068))
    : (¬ p2068) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2068 := Classical.byContradiction (fun h => hn h);
    let u1 : p1962 := h2122;
    (Or.elim h2270 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40852 (p1963 p2069 : Prop)
    (h2123 : p1963)
    (h2272 : (¬ p1963) ∨ (¬ p2069))
    : (¬ p2069) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2069 := Classical.byContradiction (fun h => hn h);
    let u1 : p1963 := h2123;
    (Or.elim h2272 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40853 (p1964 p2070 : Prop)
    (h2124 : p1964)
    (h2274 : (¬ p1964) ∨ (¬ p2070))
    : (¬ p2070) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2070 := Classical.byContradiction (fun h => hn h);
    let u1 : p1964 := h2124;
    (Or.elim h2274 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40855 (p1966 p2072 : Prop)
    (h2126 : p1966)
    (h2278 : (¬ p1966) ∨ (¬ p2072))
    : (¬ p2072) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2072 := Classical.byContradiction (fun h => hn h);
    let u1 : p1966 := h2126;
    (Or.elim h2278 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40856 (p1967 p2073 : Prop)
    (h2127 : p1967)
    (h2280 : (¬ p1967) ∨ (¬ p2073))
    : (¬ p2073) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2073 := Classical.byContradiction (fun h => hn h);
    let u1 : p1967 := h2127;
    (Or.elim h2280 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40857 (p1968 p2074 : Prop)
    (h2128 : p1968)
    (h2282 : (¬ p1968) ∨ (¬ p2074))
    : (¬ p2074) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2074 := Classical.byContradiction (fun h => hn h);
    let u1 : p1968 := h2128;
    (Or.elim h2282 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40858 (p1969 p2075 : Prop)
    (h2129 : p1969)
    (h2284 : (¬ p1969) ∨ (¬ p2075))
    : (¬ p2075) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2075 := Classical.byContradiction (fun h => hn h);
    let u1 : p1969 := h2129;
    (Or.elim h2284 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40860 (p1971 p2077 : Prop)
    (h2131 : p1971)
    (h2288 : (¬ p1971) ∨ (¬ p2077))
    : (¬ p2077) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2077 := Classical.byContradiction (fun h => hn h);
    let u1 : p1971 := h2131;
    (Or.elim h2288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40862 (p1973 p2079 : Prop)
    (h2133 : p1973)
    (h2292 : (¬ p1973) ∨ (¬ p2079))
    : (¬ p2079) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2079 := Classical.byContradiction (fun h => hn h);
    let u1 : p1973 := h2133;
    (Or.elim h2292 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u0)))))

theorem step40864 (p2028 p2114 : Prop)
    (h40811 : (¬ p2028))
    (h2364 : p2028 ∨ (¬ p2114))
    : (¬ p2114) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2114 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2028) := h40811;
    (Or.elim h2364 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40865 (p2029 p2148 : Prop)
    (h40812 : (¬ p2029))
    (h2434 : p2029 ∨ (¬ p2148))
    : (¬ p2148) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2148 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2029) := h40812;
    (Or.elim h2434 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40866 (p2030 p2169 : Prop)
    (h40813 : (¬ p2030))
    (h2476 : p2030 ∨ (¬ p2169))
    : (¬ p2169) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2169 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2030) := h40813;
    (Or.elim h2476 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40867 (p2031 p2202 : Prop)
    (h40814 : (¬ p2031))
    (h2539 : p2031 ∨ (¬ p2202))
    : (¬ p2202) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2202 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2031) := h40814;
    (Or.elim h2539 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40868 (p2032 p2233 : Prop)
    (h40815 : (¬ p2032))
    (h2601 : p2032 ∨ (¬ p2233))
    : (¬ p2233) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2233 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2032) := h40815;
    (Or.elim h2601 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40869 (p2033 p2287 : Prop)
    (h40816 : (¬ p2033))
    (h2711 : p2033 ∨ (¬ p2287))
    : (¬ p2287) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2287 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2033) := h40816;
    (Or.elim h2711 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40870 (p2034 p2323 : Prop)
    (h40817 : (¬ p2034))
    (h2782 : p2034 ∨ (¬ p2323))
    : (¬ p2323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2323 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2034) := h40817;
    (Or.elim h2782 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40871 (p2035 p2344 : Prop)
    (h40818 : (¬ p2035))
    (h2825 : p2035 ∨ (¬ p2344))
    : (¬ p2344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2344 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2035) := h40818;
    (Or.elim h2825 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40872 (p2036 p2355 : Prop)
    (h40819 : (¬ p2036))
    (h2847 : p2036 ∨ (¬ p2355))
    : (¬ p2355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2355 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2036) := h40819;
    (Or.elim h2847 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40873 (p2037 p2388 : Prop)
    (h40820 : (¬ p2037))
    (h2910 : p2037 ∨ (¬ p2388))
    : (¬ p2388) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2388 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2037) := h40820;
    (Or.elim h2910 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40874 (p2038 p2409 : Prop)
    (h40821 : (¬ p2038))
    (h2952 : p2038 ∨ (¬ p2409))
    : (¬ p2409) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2409 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2038) := h40821;
    (Or.elim h2952 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40875 (p2039 p2462 : Prop)
    (h40822 : (¬ p2039))
    (h3055 : p2039 ∨ (¬ p2462))
    : (¬ p2462) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2462 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2039) := h40822;
    (Or.elim h3055 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40876 (p2040 p2545 : Prop)
    (h40823 : (¬ p2040))
    (h3215 : p2040 ∨ (¬ p2545))
    : (¬ p2545) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2545 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2040) := h40823;
    (Or.elim h3215 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40877 (p2041 p2611 : Prop)
    (h40824 : (¬ p2041))
    (h3347 : p2041 ∨ (¬ p2611))
    : (¬ p2611) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2611 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2041) := h40824;
    (Or.elim h3347 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40878 (p2042 p2622 : Prop)
    (h40825 : (¬ p2042))
    (h3369 : p2042 ∨ (¬ p2622))
    : (¬ p2622) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2622 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2042) := h40825;
    (Or.elim h3369 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40879 (p2043 p2633 : Prop)
    (h40826 : (¬ p2043))
    (h3391 : p2043 ∨ (¬ p2633))
    : (¬ p2633) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2633 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2043) := h40826;
    (Or.elim h3391 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40880 (p2044 p2688 : Prop)
    (h40827 : (¬ p2044))
    (h3502 : p2044 ∨ (¬ p2688))
    : (¬ p2688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2688 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2044) := h40827;
    (Or.elim h3502 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40881 (p2045 p2699 : Prop)
    (h40828 : (¬ p2045))
    (h3524 : p2045 ∨ (¬ p2699))
    : (¬ p2699) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2699 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2045) := h40828;
    (Or.elim h3524 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40882 (p2046 p2764 : Prop)
    (h40829 : (¬ p2046))
    (h3655 : p2046 ∨ (¬ p2764))
    : (¬ p2764) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2764 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2046) := h40829;
    (Or.elim h3655 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40883 (p2047 p2765 : Prop)
    (h40830 : (¬ p2047))
    (h3657 : p2047 ∨ (¬ p2765))
    : (¬ p2765) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2765 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2047) := h40830;
    (Or.elim h3657 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40884 (p2048 p2766 : Prop)
    (h40831 : (¬ p2048))
    (h3659 : p2048 ∨ (¬ p2766))
    : (¬ p2766) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2766 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2048) := h40831;
    (Or.elim h3659 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40885 (p2049 p2842 : Prop)
    (h40832 : (¬ p2049))
    (h3810 : p2049 ∨ (¬ p2842))
    : (¬ p2842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2842 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2049) := h40832;
    (Or.elim h3810 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40886 (p2050 p2873 : Prop)
    (h40833 : (¬ p2050))
    (h3872 : p2050 ∨ (¬ p2873))
    : (¬ p2873) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2873 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2050) := h40833;
    (Or.elim h3872 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40887 (p2051 p2914 : Prop)
    (h40834 : (¬ p2051))
    (h3954 : p2051 ∨ (¬ p2914))
    : (¬ p2914) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2914 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2051) := h40834;
    (Or.elim h3954 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40888 (p2052 p2938 : Prop)
    (h40835 : (¬ p2052))
    (h4004 : p2052 ∨ (¬ p2938))
    : (¬ p2938) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2938 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2052) := h40835;
    (Or.elim h4004 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40889 (p2053 p2964 : Prop)
    (h40836 : (¬ p2053))
    (h4055 : p2053 ∨ (¬ p2964))
    : (¬ p2964) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2964 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2053) := h40836;
    (Or.elim h4055 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40890 (p2054 p2997 : Prop)
    (h40837 : (¬ p2054))
    (h4118 : p2054 ∨ (¬ p2997))
    : (¬ p2997) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2997 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2054) := h40837;
    (Or.elim h4118 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40891 (p2055 p3008 : Prop)
    (h40838 : (¬ p2055))
    (h4140 : p2055 ∨ (¬ p3008))
    : (¬ p3008) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3008 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2055) := h40838;
    (Or.elim h4140 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40892 (p2056 p3042 : Prop)
    (h40839 : (¬ p2056))
    (h4211 : p2056 ∨ (¬ p3042))
    : (¬ p3042) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3042 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2056) := h40839;
    (Or.elim h4211 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40893 (p2057 p3043 : Prop)
    (h40840 : (¬ p2057))
    (h4213 : p2057 ∨ (¬ p3043))
    : (¬ p3043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3043 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2057) := h40840;
    (Or.elim h4213 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40894 (p2058 p3128 : Prop)
    (h40841 : (¬ p2058))
    (h4377 : p2058 ∨ (¬ p3128))
    : (¬ p3128) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3128 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2058) := h40841;
    (Or.elim h4377 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40895 (p2059 p3360 : Prop)
    (h40842 : (¬ p2059))
    (h4831 : p2059 ∨ (¬ p3360))
    : (¬ p3360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3360 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2059) := h40842;
    (Or.elim h4831 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40896 (p2060 p3437 : Prop)
    (h40843 : (¬ p2060))
    (h4964 : p2060 ∨ (¬ p3437))
    : (¬ p3437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3437 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2060) := h40843;
    (Or.elim h4964 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40897 (p2061 p3441 : Prop)
    (h40844 : (¬ p2061))
    (h4967 : p2061 ∨ (¬ p3441))
    : (¬ p3441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3441 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2061) := h40844;
    (Or.elim h4967 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40898 (p2062 p3474 : Prop)
    (h40845 : (¬ p2062))
    (h5030 : p2062 ∨ (¬ p3474))
    : (¬ p3474) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3474 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2062) := h40845;
    (Or.elim h5030 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40899 (p2063 p3498 : Prop)
    (h40846 : (¬ p2063))
    (h5079 : p2063 ∨ (¬ p3498))
    : (¬ p3498) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3498 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2063) := h40846;
    (Or.elim h5079 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40900 (p2064 p3578 : Prop)
    (h40847 : (¬ p2064))
    (h5204 : p2064 ∨ (¬ p3578))
    : (¬ p3578) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3578 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2064) := h40847;
    (Or.elim h5204 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40901 (p2065 p3586 : Prop)
    (h40848 : (¬ p2065))
    (h5211 : p2065 ∨ (¬ p3586))
    : (¬ p3586) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3586 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2065) := h40848;
    (Or.elim h5211 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40902 (p2066 p3622 : Prop)
    (h40849 : (¬ p2066))
    (h5278 : p2066 ∨ (¬ p3622))
    : (¬ p3622) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3622 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2066) := h40849;
    (Or.elim h5278 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40903 (p2067 p3623 : Prop)
    (h40850 : (¬ p2067))
    (h5280 : p2067 ∨ (¬ p3623))
    : (¬ p3623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3623 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2067) := h40850;
    (Or.elim h5280 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40904 (p2068 p3783 : Prop)
    (h40851 : (¬ p2068))
    (h5561 : p2068 ∨ (¬ p3783))
    : (¬ p3783) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3783 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2068) := h40851;
    (Or.elim h5561 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40905 (p2069 p3818 : Prop)
    (h40852 : (¬ p2069))
    (h5632 : p2069 ∨ (¬ p3818))
    : (¬ p3818) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3818 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2069) := h40852;
    (Or.elim h5632 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40906 (p2070 p3871 : Prop)
    (h40853 : (¬ p2070))
    (h5728 : p2070 ∨ (¬ p3871))
    : (¬ p3871) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3871 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2070) := h40853;
    (Or.elim h5728 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40908 (p2072 p3944 : Prop)
    (h40855 : (¬ p2072))
    (h5855 : p2072 ∨ (¬ p3944))
    : (¬ p3944) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3944 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2072) := h40855;
    (Or.elim h5855 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40909 (p2073 p3982 : Prop)
    (h40856 : (¬ p2073))
    (h5913 : p2073 ∨ (¬ p3982))
    : (¬ p3982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3982 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2073) := h40856;
    (Or.elim h5913 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40910 (p2074 p4023 : Prop)
    (h40857 : (¬ p2074))
    (h5991 : p2074 ∨ (¬ p4023))
    : (¬ p4023) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4023 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2074) := h40857;
    (Or.elim h5991 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40911 (p2075 p4080 : Prop)
    (h40858 : (¬ p2075))
    (h6076 : p2075 ∨ (¬ p4080))
    : (¬ p4080) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4080 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2075) := h40858;
    (Or.elim h6076 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40913 (p2077 p4206 : Prop)
    (h40860 : (¬ p2077))
    (h6302 : p2077 ∨ (¬ p4206))
    : (¬ p4206) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4206 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2077) := h40860;
    (Or.elim h6302 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40915 (p2079 p4339 : Prop)
    (h40862 : (¬ p2079))
    (h6579 : p2079 ∨ (¬ p4339))
    : (¬ p4339) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4339 := Classical.byContradiction (fun h => hn h);
    let u1 : (¬ p2079) := h40862;
    (Or.elim h6579 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u0)))))

theorem step40917 (p2027 p2352 p3646 p3660 p3989 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h7139 : p2027 ∨ (¬ p2352) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4533))
    : (¬ p2352) ∨ (¬ p3646) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7139 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40919 (p2027 p2440 p2449 p3580 p4278 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h7444 : p2027 ∨ (¬ p2440) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4646))
    : (¬ p2440) ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4278) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7444 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40920 (p2027 p2307 p2584 p2588 p2589 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h7633 : p2027 ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717))
    : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p2589) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7633 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40921 (p2027 p2295 p2313 p2386 p2440 p3019 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h7661 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p4717))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h7661 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40922 (p2027 p2373 p2542 p2659 p3904 p4120 : Prop)
    (h40810 : (¬ p2027))
    (h7730 : p2027 ∨ (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p4120))
    : (¬ p2373) ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3904) ∨ (¬ p4120) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7730 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40923 (p2027 p2685 p2696 p2741 p2996 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h7899 : p2027 ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p4737))
    : (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2741) ∨ (¬ p2996) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7899 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40924 (p2027 p2299 p2396 p4261 p4443 p4832 : Prop)
    (h40810 : (¬ p2027))
    (h7917 : p2027 ∨ (¬ p2299) ∨ (¬ p2396) ∨ (¬ p4261) ∨ (¬ p4443) ∨ (¬ p4832))
    : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p4261) ∨ (¬ p4443) ∨ (¬ p4832) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4832 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7917 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40925 (p2027 p2745 p2774 p3365 p4154 p4328 : Prop)
    (h40810 : (¬ p2027))
    (h7944 : p2027 ∨ (¬ p2745) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4154) ∨ (¬ p4328))
    : (¬ p2745) ∨ (¬ p2774) ∨ (¬ p3365) ∨ (¬ p4154) ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7944 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40926 (p2027 p2253 p2750 p2807 p3954 p4111 p4112 : Prop)
    (h40810 : (¬ p2027))
    (h7962 : p2027 ∨ (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2807) ∨ (¬ p3954) ∨ (¬ p4111) ∨ (¬ p4112))
    : (¬ p2253) ∨ (¬ p2750) ∨ (¬ p2807) ∨ (¬ p3954) ∨ (¬ p4111) ∨ (¬ p4112) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h7962 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40927 (p2027 p2598 p3365 p3572 p3683 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h7980 : p2027 ∨ (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3683) ∨ (¬ p4650))
    : (¬ p2598) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3683) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h7980 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40928 (p2027 p2146 p2839 p3051 p3588 p4169 : Prop)
    (h40810 : (¬ p2027))
    (h8083 : p2027 ∨ (¬ p2146) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3588) ∨ (¬ p4169))
    : (¬ p2146) ∨ (¬ p2839) ∨ (¬ p3051) ∨ (¬ p3588) ∨ (¬ p4169) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8083 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40931 (p2027 p2563 p2946 p2963 p3745 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h8203 : p2027 ∨ (¬ p2563) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4702))
    : (¬ p2563) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8203 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40932 (p2027 p3027 p3574 p3579 p4111 p4711 : Prop)
    (h40810 : (¬ p2027))
    (h8310 : p2027 ∨ (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4711))
    : (¬ p3027) ∨ (¬ p3574) ∨ (¬ p3579) ∨ (¬ p4111) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3027 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8310 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40933 (p2027 p2745 p2870 p2957 p3556 p3662 p4313 : Prop)
    (h40810 : (¬ p2027))
    (h8312 : p2027 ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p4313))
    : (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h8312 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40934 (p2027 p2230 p2440 p2663 p2963 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h8331 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2963) ∨ (¬ p4972))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p2963) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8331 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40935 (p2027 p2459 p2881 p3544 p4261 p4911 : Prop)
    (h40810 : (¬ p2027))
    (h8366 : p2027 ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4911))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3544) ∨ (¬ p4261) ∨ (¬ p4911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8366 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40936 (p2027 p2598 p2745 p3365 p3683 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h8402 : p2027 ∨ (¬ p2598) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4111))
    : (¬ p2598) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3683) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8402 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40937 (p2027 p2963 p3166 p3923 p4417 p4757 : Prop)
    (h40810 : (¬ p2027))
    (h8531 : p2027 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3923) ∨ (¬ p4417) ∨ (¬ p4757))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3923) ∨ (¬ p4417) ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8531 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40938 (p2027 p2449 p2922 p3193 p4636 p4653 : Prop)
    (h40810 : (¬ p2027))
    (h8549 : p2027 ∨ (¬ p2449) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4636) ∨ (¬ p4653))
    : (¬ p2449) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4636) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8549 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40939 (p2027 p2459 p2619 p3949 p4133 p4385 p4441 : Prop)
    (h40810 : (¬ p2027))
    (h8567 : p2027 ∨ (¬ p2459) ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p4133) ∨ (¬ p4385) ∨ (¬ p4441))
    : (¬ p2459) ∨ (¬ p2619) ∨ (¬ p3949) ∨ (¬ p4133) ∨ (¬ p4385) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h8567 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40940 (p2027 p2528 p3570 p3875 p4348 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h8624 : p2027 ∨ (¬ p2528) ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4647))
    : (¬ p2528) ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8624 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40941 (p2027 p2088 p3266 p3657 p4381 p4592 : Prop)
    (h40810 : (¬ p2027))
    (h8643 : p2027 ∨ (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4592))
    : (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4592) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8643 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40942 (p2027 p3276 p3358 p4348 p4438 p4444 : Prop)
    (h40810 : (¬ p2027))
    (h8661 : p2027 ∨ (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4444))
    : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8661 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40943 (p2027 p3172 p3286 p4347 p4350 p4774 : Prop)
    (h40810 : (¬ p2027))
    (h8700 : p2027 ∨ (¬ p3172) ∨ (¬ p3286) ∨ (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774))
    : (¬ p3172) ∨ (¬ p3286) ∨ (¬ p4347) ∨ (¬ p4350) ∨ (¬ p4774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4350 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8700 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40944 (p2027 p2528 p3063 p4026 p4171 p4384 : Prop)
    (h40810 : (¬ p2027))
    (h8738 : p2027 ∨ (¬ p2528) ∨ (¬ p3063) ∨ (¬ p4026) ∨ (¬ p4171) ∨ (¬ p4384))
    : (¬ p2528) ∨ (¬ p3063) ∨ (¬ p4026) ∨ (¬ p4171) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8738 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40945 (p2027 p3333 p3359 p3475 p4195 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h8756 : p2027 ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3475) ∨ (¬ p4195) ∨ (¬ p4972))
    : (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3475) ∨ (¬ p4195) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8756 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40946 (p2027 p2476 p3355 p4348 p4438 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h8791 : p2027 ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695))
    : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8791 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40947 (p2027 p2743 p3367 p3683 p4315 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h8792 : p2027 ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4315) ∨ (¬ p4701))
    : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4315) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8792 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40948 (p2027 p2741 p2811 p2946 p3367 p3662 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h8793 : p2027 ∨ (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p4752))
    : (¬ p2741) ∨ (¬ p2811) ∨ (¬ p2946) ∨ (¬ p3367) ∨ (¬ p3662) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h8793 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40949 (p2027 p2630 p2737 p3688 p4337 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h8795 : p2027 ∨ (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4972))
    : (¬ p2630) ∨ (¬ p2737) ∨ (¬ p3688) ∨ (¬ p4337) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8795 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40950 (p2027 p2743 p3367 p3683 p4195 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h8796 : p2027 ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4195) ∨ (¬ p4972))
    : (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4195) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8796 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40951 (p2027 p2241 p2727 p3032 p4366 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h8848 : p2027 ∨ (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3032) ∨ (¬ p4366) ∨ (¬ p4650))
    : (¬ p2241) ∨ (¬ p2727) ∨ (¬ p3032) ∨ (¬ p4366) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8848 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40952 (p2027 p2241 p2254 p3027 p3414 : Prop)
    (h40810 : (¬ p2027))
    (h8849 : p2027 ∨ (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3414))
    : (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3414) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h8849 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step40953 (p2027 p2247 p3379 p3487 p3662 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h8850 : p2027 ∨ (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3662) ∨ (¬ p4701))
    : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p3662) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8850 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40954 (p2027 p2437 p2727 p3662 p3879 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h8868 : p2027 ∨ (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646))
    : (¬ p2437) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8868 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40956 (p2027 p2598 p3005 p3172 p4236 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h8888 : p2027 ∨ (¬ p2598) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4752))
    : (¬ p2598) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p4236) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8888 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40957 (p2027 p2651 p2780 p2810 p4117 p4842 : Prop)
    (h40810 : (¬ p2027))
    (h8889 : p2027 ∨ (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4842))
    : (¬ p2651) ∨ (¬ p2780) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8889 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40958 (p2027 p2299 p2319 p2341 p2788 p3822 : Prop)
    (h40810 : (¬ p2027))
    (h8890 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2788) ∨ (¬ p3822))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2788) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2788 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40959 (p2027 p2518 p2651 p3172 p4437 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h8908 : p2027 ∨ (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4437) ∨ (¬ p4814))
    : (¬ p2518) ∨ (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4437) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8908 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40960 (p2027 p2696 p2751 p3027 p3425 p4777 : Prop)
    (h40810 : (¬ p2027))
    (h8978 : p2027 ∨ (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p4777))
    : (¬ p2696) ∨ (¬ p2751) ∨ (¬ p3027) ∨ (¬ p3425) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8978 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40961 (p2027 p2210 p3452 p3684 p4210 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h8998 : p2027 ∨ (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p5217))
    : (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h8998 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40962 (p2027 p2122 p2341 p3575 p4138 p4358 p4712 : Prop)
    (h40810 : (¬ p2027))
    (h9034 : p2027 ∨ (¬ p2122) ∨ (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4712))
    : (¬ p2122) ∨ (¬ p2341) ∨ (¬ p3575) ∨ (¬ p4138) ∨ (¬ p4358) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9034 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40963 (p2027 p2299 p2319 p2341 p2586 p2588 : Prop)
    (h40810 : (¬ p2027))
    (h9055 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2586) ∨ (¬ p2588))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2586) ∨ (¬ p2588) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9055 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40964 (p2027 p3367 p3389 p3588 p4106 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9056 : p2027 ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4730))
    : (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3588) ∨ (¬ p4106) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4106 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9056 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40965 (p2027 p2493 p2630 p4195 p4389 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h9057 : p2027 ∨ (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4814))
    : (¬ p2493) ∨ (¬ p2630) ∨ (¬ p4195) ∨ (¬ p4389) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40966 (p2027 p2470 p2509 p3954 p4079 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h9058 : p2027 ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216))
    : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9058 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40967 (p2027 p2247 p3379 p3487 p4154 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h9076 : p2027 ∨ (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4154) ∨ (¬ p4972))
    : (¬ p2247) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4154) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40968 (p2027 p2245 p2749 p3172 p3189 p3379 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h9077 : p2027 ∨ (¬ p2245) ∨ (¬ p2749) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3379) ∨ (¬ p5216))
    : (¬ p2245) ∨ (¬ p2749) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p3379) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40969 (p2027 p2146 p2881 p3051 p3659 p4136 : Prop)
    (h40810 : (¬ p2027))
    (h9078 : p2027 ∨ (¬ p2146) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3659) ∨ (¬ p4136))
    : (¬ p2146) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3659) ∨ (¬ p4136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9078 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40970 (p2027 p2651 p2850 p2952 p3879 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h9079 : p2027 ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4753))
    : (¬ p2651) ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3879) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9079 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40971 (p2027 p2341 p2685 p2745 p3031 p3548 p4066 : Prop)
    (h40810 : (¬ p2027))
    (h9081 : p2027 ∨ (¬ p2341) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4066))
    : (¬ p2341) ∨ (¬ p2685) ∨ (¬ p2745) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p4066) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9081 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40972 (p2027 p2299 p2319 p2341 p3549 p5022 : Prop)
    (h40810 : (¬ p2027))
    (h9082 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3549) ∨ (¬ p5022))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3549) ∨ (¬ p5022) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9082 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40974 (p2027 p2668 p3548 p3550 p3568 p5142 : Prop)
    (h40810 : (¬ p2027))
    (h9085 : p2027 ∨ (¬ p2668) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p5142))
    : (¬ p2668) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p5142) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9085 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40975 (p2027 p2427 p2881 p3548 p3554 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h9086 : p2027 ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629))
    : (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9086 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40976 (p2027 p2192 p2881 p3548 p3554 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9087 : p2027 ∨ (¬ p2192) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4555))
    : (¬ p2192) ∨ (¬ p2881) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9087 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40977 (p2027 p2187 p3097 p3548 p3550 p5142 : Prop)
    (h40810 : (¬ p2027))
    (h9088 : p2027 ∨ (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p5142))
    : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p5142) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9088 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40978 (p2027 p2933 p3238 p3399 p3452 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h9089 : p2027 ∨ (¬ p2933) ∨ (¬ p3238) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4646))
    : (¬ p2933) ∨ (¬ p3238) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9089 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40980 (p2027 p2341 p2459 p3692 p4119 p4990 : Prop)
    (h40810 : (¬ p2027))
    (h9091 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4990))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9091 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40982 (p2027 p2352 p2459 p4133 p4137 p4171 : Prop)
    (h40810 : (¬ p2027))
    (h9093 : p2027 ∨ (¬ p2352) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4137) ∨ (¬ p4171))
    : (¬ p2352) ∨ (¬ p2459) ∨ (¬ p4133) ∨ (¬ p4137) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9093 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40983 (p2027 p3105 p3238 p3582 p4948 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h9094 : p2027 ∨ (¬ p3105) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4948) ∨ (¬ p5214))
    : (¬ p3105) ∨ (¬ p3238) ∨ (¬ p3582) ∨ (¬ p4948) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9094 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40985 (p2027 p2437 p2911 p2926 p3548 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9099 : p2027 ∨ (¬ p2437) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4811))
    : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9099 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40986 (p2027 p2264 p3574 p3580 p3644 p4711 : Prop)
    (h40810 : (¬ p2027))
    (h9117 : p2027 ∨ (¬ p2264) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4711))
    : (¬ p2264) ∨ (¬ p3574) ∨ (¬ p3580) ∨ (¬ p3644) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9117 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40988 (p2027 p3005 p3034 p3171 p3548 p3572 p4403 : Prop)
    (h40810 : (¬ p2027))
    (h9119 : p2027 ∨ (¬ p3005) ∨ (¬ p3034) ∨ (¬ p3171) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4403))
    : (¬ p3005) ∨ (¬ p3034) ∨ (¬ p3171) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9119 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40989 (p2027 p3034 p3166 p3414 p3548 p4378 : Prop)
    (h40810 : (¬ p2027))
    (h9120 : p2027 ∨ (¬ p3034) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4378))
    : (¬ p3034) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3034 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9120 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40990 (p2027 p2331 p2499 p2657 p3984 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9122 : p2027 ∨ (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4811))
    : (¬ p2331) ∨ (¬ p2499) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9122 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40991 (p2027 p2470 p2588 p2656 p3574 p4157 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h9123 : p2027 ∨ (¬ p2470) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p4157) ∨ (¬ p4405))
    : (¬ p2470) ∨ (¬ p2588) ∨ (¬ p2656) ∨ (¬ p3574) ∨ (¬ p4157) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9123 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step40992 (p2027 p2177 p2307 p2586 p3581 p3644 : Prop)
    (h40810 : (¬ p2027))
    (h9124 : p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p3644))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9124 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40993 (p2027 p2922 p3238 p3569 p3880 p4901 : Prop)
    (h40810 : (¬ p2027))
    (h9126 : p2027 ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p3880) ∨ (¬ p4901))
    : (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p3880) ∨ (¬ p4901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9126 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40994 (p2027 p2341 p2427 p3880 p4132 p4990 : Prop)
    (h40810 : (¬ p2027))
    (h9127 : p2027 ∨ (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4990))
    : (¬ p2341) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9127 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40995 (p2027 p2331 p2901 p2950 p3556 p4566 : Prop)
    (h40810 : (¬ p2027))
    (h9128 : p2027 ∨ (¬ p2331) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4566))
    : (¬ p2331) ∨ (¬ p2901) ∨ (¬ p2950) ∨ (¬ p3556) ∨ (¬ p4566) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9128 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40997 (p2027 p2641 p3497 p3662 p3986 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h9130 : p2027 ∨ (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4507))
    : (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9130 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40998 (p2027 p2264 p2459 p2534 p4186 p4653 : Prop)
    (h40810 : (¬ p2027))
    (h9131 : p2027 ∨ (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p4653))
    : (¬ p2264) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p4653) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9131 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step40999 (p2027 p2363 p3325 p3548 p4348 p5142 : Prop)
    (h40810 : (¬ p2027))
    (h9132 : p2027 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p5142))
    : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3548) ∨ (¬ p4348) ∨ (¬ p5142) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9132 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41000 (p2027 p2717 p3471 p3548 p4400 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h9133 : p2027 ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4737))
    : (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3548) ∨ (¬ p4400) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9133 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41001 (p2027 p2230 p3362 p3585 p3684 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h9135 : p2027 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4737))
    : (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9135 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41002 (p2027 p2230 p3367 p3583 p3698 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9136 : p2027 ∨ (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4730))
    : (¬ p2230) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9136 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41003 (p2027 p2749 p2952 p2992 p3361 p3585 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h9137 : p2027 ∨ (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p4749))
    : (¬ p2749) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3361) ∨ (¬ p3585) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2749 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9137 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41004 (p2027 p2341 p3644 p3876 p4730 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h9139 : p2027 ∨ (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4730) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4730) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9139 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41005 (p2027 p2210 p2247 p2751 p4282 p4315 : Prop)
    (h40810 : (¬ p2027))
    (h9140 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p4282) ∨ (¬ p4315))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2751) ∨ (¬ p4282) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2751 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9140 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41006 (p2027 p2247 p2598 p2744 p3585 p3589 : Prop)
    (h40810 : (¬ p2027))
    (h9141 : p2027 ∨ (¬ p2247) ∨ (¬ p2598) ∨ (¬ p2744) ∨ (¬ p3585) ∨ (¬ p3589))
    : (¬ p2247) ∨ (¬ p2598) ∨ (¬ p2744) ∨ (¬ p3585) ∨ (¬ p3589) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9141 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41007 (p2027 p2247 p2608 p2742 p3367 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h9142 : p2027 ∨ (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p3367) ∨ (¬ p4752))
    : (¬ p2247) ∨ (¬ p2608) ∨ (¬ p2742) ∨ (¬ p3367) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9142 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41008 (p2027 p2132 p2630 p2657 p4236 p5052 : Prop)
    (h40810 : (¬ p2027))
    (h9143 : p2027 ∨ (¬ p2132) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p5052))
    : (¬ p2132) ∨ (¬ p2630) ∨ (¬ p2657) ∨ (¬ p4236) ∨ (¬ p5052) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9143 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41010 (p2027 p2598 p2850 p3238 p4257 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h9147 : p2027 ∨ (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4737))
    : (¬ p2598) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9147 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41011 (p2027 p2891 p3684 p3948 p4235 p5217 : Prop)
    (h40810 : (¬ p2027))
    (h9148 : p2027 ∨ (¬ p2891) ∨ (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5217))
    : (¬ p2891) ∨ (¬ p3684) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9148 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41012 (p2027 p2829 p3583 p4185 p4385 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h9149 : p2027 ∨ (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4385) ∨ (¬ p5043))
    : (¬ p2829) ∨ (¬ p3583) ∨ (¬ p4185) ∨ (¬ p4385) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9149 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41015 (p2027 p2254 p2608 p2707 p2963 p3324 p3434 p3950 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h9208 : p2027 ∨ (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4347))
    : (¬ p2254) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3434) ∨ (¬ p3950) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h9208 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41016 (p2027 p2839 p3585 p3695 p3876 p4644 : Prop)
    (h40810 : (¬ p2027))
    (h9226 : p2027 ∨ (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p3876) ∨ (¬ p4644))
    : (¬ p2839) ∨ (¬ p3585) ∨ (¬ p3695) ∨ (¬ p3876) ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9226 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41017 (p2027 p2829 p2901 p3588 p4169 p4193 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h9227 : p2027 ∨ (¬ p2829) ∨ (¬ p2901) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4193) ∨ (¬ p4906))
    : (¬ p2829) ∨ (¬ p2901) ∨ (¬ p3588) ∨ (¬ p4169) ∨ (¬ p4193) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9227 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41018 (p2027 p2156 p2254 p2952 p3952 p4172 : Prop)
    (h40810 : (¬ p2027))
    (h9228 : p2027 ∨ (¬ p2156) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4172))
    : (¬ p2156) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3952) ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9228 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41019 (p2027 p3093 p3555 p4110 p4516 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h9229 : p2027 ∨ (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4110) ∨ (¬ p4516) ∨ (¬ p4632))
    : (¬ p3093) ∨ (¬ p3555) ∨ (¬ p4110) ∨ (¬ p4516) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9229 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41020 (p2027 p3156 p3644 p4042 p4277 p4320 : Prop)
    (h40810 : (¬ p2027))
    (h9230 : p2027 ∨ (¬ p3156) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) ∨ (¬ p4320))
    : (¬ p3156) ∨ (¬ p3644) ∨ (¬ p4042) ∨ (¬ p4277) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9230 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41021 (p2027 p2341 p2459 p2534 p4186 p5203 : Prop)
    (h40810 : (¬ p2027))
    (h9231 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p5203))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2534) ∨ (¬ p4186) ∨ (¬ p5203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9231 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41022 (p2027 p2341 p2707 p4242 p4800 p5261 : Prop)
    (h40810 : (¬ p2027))
    (h9232 : p2027 ∨ (¬ p2341) ∨ (¬ p2707) ∨ (¬ p4242) ∨ (¬ p4800) ∨ (¬ p5261))
    : (¬ p2341) ∨ (¬ p2707) ∨ (¬ p4242) ∨ (¬ p4800) ∨ (¬ p5261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4800 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9232 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41023 (p2027 p2341 p3201 p3874 p4383 p5203 : Prop)
    (h40810 : (¬ p2027))
    (h9250 : p2027 ∨ (¬ p2341) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p4383) ∨ (¬ p5203))
    : (¬ p2341) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p4383) ∨ (¬ p5203) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9250 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41024 (p2027 p2341 p2952 p3037 p3548 p4104 p4919 : Prop)
    (h40810 : (¬ p2027))
    (h9251 : p2027 ∨ (¬ p2341) ∨ (¬ p2952) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4919))
    : (¬ p2341) ∨ (¬ p2952) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9251 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41025 (p2027 p2230 p2563 p3054 p4173 p4243 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9252 : p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4730))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p4173) ∨ (¬ p4243) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9252 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41026 (p2027 p2319 p2341 p3547 p3548 p3946 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h9270 : p2027 ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3547) ∨ (¬ p3548) ∨ (¬ p3946) ∨ (¬ p4620))
    : (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3547) ∨ (¬ p3548) ∨ (¬ p3946) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9270 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41027 (p2027 p2573 p3367 p3688 p4342 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9271 : p2027 ∨ (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4730))
    : (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3688) ∨ (¬ p4342) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4342 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9271 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41028 (p2027 p2307 p2396 p2586 p3581 p4278 : Prop)
    (h40810 : (¬ p2027))
    (h9272 : p2027 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p4278))
    : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2586) ∨ (¬ p3581) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9272 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41030 (p2027 p3256 p3659 p3857 p4044 p4403 p4779 : Prop)
    (h40810 : (¬ p2027))
    (h9274 : p2027 ∨ (¬ p3256) ∨ (¬ p3659) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4403) ∨ (¬ p4779))
    : (¬ p3256) ∨ (¬ p3659) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4403) ∨ (¬ p4779) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9274 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41031 (p2027 p2088 p3659 p4348 p4590 p5261 : Prop)
    (h40810 : (¬ p2027))
    (h9275 : p2027 ∨ (¬ p2088) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p5261))
    : (¬ p2088) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p5261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9275 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41032 (p2027 p2230 p2255 p2440 p2663 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h9276 : p2027 ∨ (¬ p2230) ∨ (¬ p2255) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p4111))
    : (¬ p2230) ∨ (¬ p2255) ∨ (¬ p2440) ∨ (¬ p2663) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9276 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41033 (p2027 p2230 p2665 p2727 p3662 p3879 : Prop)
    (h40810 : (¬ p2027))
    (h9277 : p2027 ∨ (¬ p2230) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879))
    : (¬ p2230) ∨ (¬ p2665) ∨ (¬ p2727) ∨ (¬ p3662) ∨ (¬ p3879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9277 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41035 (p2027 p2284 p3189 p3368 p4173 p5065 : Prop)
    (h40810 : (¬ p2027))
    (h9279 : p2027 ∨ (¬ p2284) ∨ (¬ p3189) ∨ (¬ p3368) ∨ (¬ p4173) ∨ (¬ p5065))
    : (¬ p2284) ∨ (¬ p3189) ∨ (¬ p3368) ∨ (¬ p4173) ∨ (¬ p5065) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5065 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9279 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41036 (p2027 p2542 p2651 p3364 p3684 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h9280 : p2027 ∨ (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4790))
    : (¬ p2542) ∨ (¬ p2651) ∨ (¬ p3364) ∨ (¬ p3684) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9280 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41037 (p2027 p2641 p3662 p3986 p4208 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h9281 : p2027 ∨ (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p5043))
    : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p3986) ∨ (¬ p4208) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9281 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41038 (p2027 p2177 p2553 p3548 p3576 p3689 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h9282 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3689) ∨ (¬ p5222))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p3576) ∨ (¬ p3689) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9282 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41039 (p2027 p2284 p2946 p3758 p4392 p4790 : Prop)
    (h40810 : (¬ p2027))
    (h9283 : p2027 ∨ (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4790))
    : (¬ p2284) ∨ (¬ p2946) ∨ (¬ p3758) ∨ (¬ p4392) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9283 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41041 (p2027 p2352 p2588 p3037 p3548 p3550 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h9285 : p2027 ∨ (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p4570))
    : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3037) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9285 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41042 (p2027 p3461 p4187 p4324 p4381 p4473 : Prop)
    (h40810 : (¬ p2027))
    (h9287 : p2027 ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4473))
    : (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4473) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9287 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41043 (p2027 p2911 p3434 p3659 p3947 p4327 : Prop)
    (h40810 : (¬ p2027))
    (h9288 : p2027 ∨ (¬ p2911) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3947) ∨ (¬ p4327))
    : (¬ p2911) ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3947) ∨ (¬ p4327) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9288 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41044 (p2027 p3564 p3956 p4345 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h9323 : p2027 ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9323 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41045 (p2027 p2518 p2928 p3570 p4404 p4647 : Prop)
    (h40810 : (¬ p2027))
    (h9324 : p2027 ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3570) ∨ (¬ p4404) ∨ (¬ p4647))
    : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p3570) ∨ (¬ p4404) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9324 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41047 (p2027 p2230 p2427 p3054 p4244 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9326 : p2027 ∨ (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3054) ∨ (¬ p4244) ∨ (¬ p4730))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p3054) ∨ (¬ p4244) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9326 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41048 (p2027 p2220 p3556 p3659 p4042 p4895 : Prop)
    (h40810 : (¬ p2027))
    (h9327 : p2027 ∨ (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3659) ∨ (¬ p4042) ∨ (¬ p4895))
    : (¬ p2220) ∨ (¬ p3556) ∨ (¬ p3659) ∨ (¬ p4042) ∨ (¬ p4895) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9327 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41050 (p2027 p2341 p2656 p2797 p3659 p4357 p4975 p5201 : Prop)
    (h40810 : (¬ p2027))
    (h9330 : p2027 ∨ (¬ p2341) ∨ (¬ p2656) ∨ (¬ p2797) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4975) ∨ (¬ p5201))
    : (¬ p2341) ∨ (¬ p2656) ∨ (¬ p2797) ∨ (¬ p3659) ∨ (¬ p4357) ∨ (¬ p4975) ∨ (¬ p5201) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9330 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41051 (p2027 p2493 p3238 p4203 p4235 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9332 : p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9332 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41053 (p2027 p2138 p2608 p2707 p3582 p3873 p5086 : Prop)
    (h40810 : (¬ p2027))
    (h9334 : p2027 ∨ (¬ p2138) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3582) ∨ (¬ p3873) ∨ (¬ p5086))
    : (¬ p2138) ∨ (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3582) ∨ (¬ p3873) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3582 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9334 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41054 (p2027 p3323 p3568 p4324 p4473 p4623 : Prop)
    (h40810 : (¬ p2027))
    (h9335 : p2027 ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4324) ∨ (¬ p4473) ∨ (¬ p4623))
    : (¬ p3323) ∨ (¬ p3568) ∨ (¬ p4324) ∨ (¬ p4473) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9335 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41055 (p2027 p3461 p4187 p4276 p4278 p4381 : Prop)
    (h40810 : (¬ p2027))
    (h9336 : p2027 ∨ (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4381))
    : (¬ p3461) ∨ (¬ p4187) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9336 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41056 (p2027 p2230 p3054 p3727 p4730 p5421 : Prop)
    (h40810 : (¬ p2027))
    (h9371 : p2027 ∨ (¬ p2230) ∨ (¬ p3054) ∨ (¬ p3727) ∨ (¬ p4730) ∨ (¬ p5421))
    : (¬ p2230) ∨ (¬ p3054) ∨ (¬ p3727) ∨ (¬ p4730) ∨ (¬ p5421) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9371 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41057 (p2027 p2493 p3238 p4203 p5433 p5440 : Prop)
    (h40810 : (¬ p2027))
    (h9389 : p2027 ∨ (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440))
    : (¬ p2493) ∨ (¬ p3238) ∨ (¬ p4203) ∨ (¬ p5433) ∨ (¬ p5440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9389 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41058 (p2027 p2922 p3238 p3569 p4948 p5102 : Prop)
    (h40810 : (¬ p2027))
    (h9407 : p2027 ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4948) ∨ (¬ p5102))
    : (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3569) ∨ (¬ p4948) ∨ (¬ p5102) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5102 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9407 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41059 (p2027 p2230 p2982 p3054 p4385 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9408 : p2027 ∨ (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3054) ∨ (¬ p4385) ∨ (¬ p4730))
    : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3054) ∨ (¬ p4385) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9408 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41060 (p2027 p2138 p3471 p3486 p4344 p4875 : Prop)
    (h40810 : (¬ p2027))
    (h9409 : p2027 ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3486) ∨ (¬ p4344) ∨ (¬ p4875))
    : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3486) ∨ (¬ p4344) ∨ (¬ p4875) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9409 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41061 (p2027 p2807 p2952 p4235 p4333 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h9410 : p2027 ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p4235) ∨ (¬ p4333) ∨ (¬ p4705))
    : (¬ p2807) ∨ (¬ p2952) ∨ (¬ p4235) ∨ (¬ p4333) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9410 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41062 (p2027 p3367 p3422 p3583 p3698 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h9411 : p2027 ∨ (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4717))
    : (¬ p3367) ∨ (¬ p3422) ∨ (¬ p3583) ∨ (¬ p3698) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9411 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41064 (p2027 p2427 p2573 p3556 p3904 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h9413 : p2027 ∨ (¬ p2427) ∨ (¬ p2573) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4717))
    : (¬ p2427) ∨ (¬ p2573) ∨ (¬ p3556) ∨ (¬ p3904) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9413 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41065 (p2027 p3212 p3684 p4399 p4730 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h9414 : p2027 ∨ (¬ p3212) ∨ (¬ p3684) ∨ (¬ p4399) ∨ (¬ p4730) ∨ (¬ p4948))
    : (¬ p3212) ∨ (¬ p3684) ∨ (¬ p4399) ∨ (¬ p4730) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9414 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41066 (p2027 p2156 p3684 p4110 p4399 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h9417 : p2027 ∨ (¬ p2156) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4730))
    : (¬ p2156) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4399) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9417 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41067 (p2027 p2341 p2509 p2922 p3577 p4383 p5087 : Prop)
    (h40810 : (¬ p2027))
    (h9418 : p2027 ∨ (¬ p2341) ∨ (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3577) ∨ (¬ p4383) ∨ (¬ p5087))
    : (¬ p2341) ∨ (¬ p2509) ∨ (¬ p2922) ∨ (¬ p3577) ∨ (¬ p4383) ∨ (¬ p5087) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5087 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9418 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41068 (p2027 p2274 p2588 p2590 p2860 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h9419 : p2027 ∨ (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2860) ∨ (¬ p4885))
    : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p2860) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9419 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41069 (p2027 p2341 p2870 p3548 p3554 p3691 p4875 : Prop)
    (h40810 : (¬ p2027))
    (h9420 : p2027 ∨ (¬ p2341) ∨ (¬ p2870) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p3691) ∨ (¬ p4875))
    : (¬ p2341) ∨ (¬ p2870) ∨ (¬ p3548) ∨ (¬ p3554) ∨ (¬ p3691) ∨ (¬ p4875) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3554 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9420 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41072 (p2027 p2542 p2563 p3742 p4001 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9442 : p2027 ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4555))
    : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3742) ∨ (¬ p4001) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9442 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41073 (p2027 p2930 p3083 p3548 p3742 p4404 : Prop)
    (h40810 : (¬ p2027))
    (h9443 : p2027 ∨ (¬ p2930) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4404))
    : (¬ p2930) ∨ (¬ p3083) ∨ (¬ p3548) ∨ (¬ p3742) ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2930 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9443 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41074 (p2027 p2230 p2417 p3821 p4644 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h9444 : p2027 ∨ (¬ p2230) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4644) ∨ (¬ p5197))
    : (¬ p2230) ∨ (¬ p2417) ∨ (¬ p3821) ∨ (¬ p4644) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9444 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41076 (p2027 p2313 p2417 p2581 p3920 p4107 : Prop)
    (h40810 : (¬ p2027))
    (h9447 : p2027 ∨ (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2581) ∨ (¬ p3920) ∨ (¬ p4107))
    : (¬ p2313) ∨ (¬ p2417) ∨ (¬ p2581) ∨ (¬ p3920) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9447 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41077 (p2027 p2341 p3027 p4360 p4548 p4854 : Prop)
    (h40810 : (¬ p2027))
    (h9448 : p2027 ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4854))
    : (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4854) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9448 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41078 (p2027 p2341 p2493 p2926 p3548 p3575 p3741 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h9449 : p2027 ∨ (¬ p2341) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4717))
    : (¬ p2341) ∨ (¬ p2493) ∨ (¬ p2926) ∨ (¬ p3548) ∨ (¬ p3575) ∨ (¬ p3741) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9449 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41079 (p2027 p2657 p2946 p3238 p4241 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9450 : p2027 ∨ (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3238) ∨ (¬ p4241) ∨ (¬ p4811))
    : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3238) ∨ (¬ p4241) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9450 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41080 (p2027 p2396 p2761 p3579 p4276 p4429 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h9478 : p2027 ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4429) ∨ (¬ p5284))
    : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3579) ∨ (¬ p4276) ∨ (¬ p4429) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9478 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41082 (p2027 p2230 p3362 p3365 p3684 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h9518 : p2027 ∨ (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3684) ∨ (¬ p4752))
    : (¬ p2230) ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3684) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9518 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41083 (p2027 p2230 p2247 p3238 p4079 p4813 : Prop)
    (h40810 : (¬ p2027))
    (h9519 : p2027 ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4813))
    : (¬ p2230) ∨ (¬ p2247) ∨ (¬ p3238) ∨ (¬ p4079) ∨ (¬ p4813) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4813 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9519 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41085 (p2027 p2588 p2807 p2963 p3552 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h9521 : p2027 ∨ (¬ p2588) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p4976))
    : (¬ p2588) ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3552) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9521 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41086 (p2027 p2761 p3246 p4025 p4191 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h9522 : p2027 ∨ (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4559))
    : (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9522 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41087 (p2027 p3680 p3947 p4192 p4280 p4381 : Prop)
    (h40810 : (¬ p2027))
    (h9523 : p2027 ∨ (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4192) ∨ (¬ p4280) ∨ (¬ p4381))
    : (¬ p3680) ∨ (¬ p3947) ∨ (¬ p4192) ∨ (¬ p4280) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3680 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9523 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41088 (p2027 p2470 p2930 p3540 p3548 p4404 : Prop)
    (h40810 : (¬ p2027))
    (h9524 : p2027 ∨ (¬ p2470) ∨ (¬ p2930) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4404))
    : (¬ p2470) ∨ (¬ p2930) ∨ (¬ p3540) ∨ (¬ p3548) ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9524 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41089 (p2027 p2696 p3434 p3820 p3821 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h9525 : p2027 ∨ (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4778))
    : (¬ p2696) ∨ (¬ p3434) ∨ (¬ p3820) ∨ (¬ p3821) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9525 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41090 (p2027 p2383 p2493 p2509 p2586 p4432 : Prop)
    (h40810 : (¬ p2027))
    (h9526 : p2027 ∨ (¬ p2383) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2586) ∨ (¬ p4432))
    : (¬ p2383) ∨ (¬ p2493) ∨ (¬ p2509) ∨ (¬ p2586) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9526 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41091 (p2027 p2911 p3201 p3553 p4112 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h9527 : p2027 ∨ (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4753))
    : (¬ p2911) ∨ (¬ p3201) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9527 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41092 (p2027 p3362 p3365 p3389 p3876 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h9528 : p2027 ∨ (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4752))
    : (¬ p3362) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3362 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9528 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41094 (p2027 p2475 p2930 p3548 p3641 p3876 p4403 : Prop)
    (h40810 : (¬ p2027))
    (h9575 : p2027 ∨ (¬ p2475) ∨ (¬ p2930) ∨ (¬ p3548) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4403))
    : (¬ p2475) ∨ (¬ p2930) ∨ (¬ p3548) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2475 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2930 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9575 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41095 (p2027 p2230 p2780 p3362 p3684 p5221 : Prop)
    (h40810 : (¬ p2027))
    (h9578 : p2027 ∨ (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p5221))
    : (¬ p2230) ∨ (¬ p2780) ∨ (¬ p3362) ∨ (¬ p3684) ∨ (¬ p5221) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9578 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41096 (p2027 p2930 p3355 p3540 p3817 p4451 : Prop)
    (h40810 : (¬ p2027))
    (h9579 : p2027 ∨ (¬ p2930) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3817) ∨ (¬ p4451))
    : (¬ p2930) ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3817) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2930 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9579 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41100 (p2027 p3192 p3276 p3947 p4327 p4381 : Prop)
    (h40810 : (¬ p2027))
    (h9600 : p2027 ∨ (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4381))
    : (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9600 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41103 (p2027 p2383 p2952 p3324 p3987 p4566 : Prop)
    (h40810 : (¬ p2027))
    (h9603 : p2027 ∨ (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4566))
    : (¬ p2383) ∨ (¬ p2952) ∨ (¬ p3324) ∨ (¬ p3987) ∨ (¬ p4566) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9603 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41104 (p2027 p2499 p2573 p2630 p2656 p2745 p3402 : Prop)
    (h40810 : (¬ p2027))
    (h9604 : p2027 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402))
    : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9604 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41105 (p2027 p2589 p2662 p2850 p3475 p3572 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h9605 : p2027 ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p4650))
    : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p3572) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9605 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41106 (p2027 p3422 p3684 p4203 p4235 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9607 : p2027 ∨ (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p3422) ∨ (¬ p3684) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9607 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41107 (p2027 p2696 p3136 p3425 p4777 p4917 : Prop)
    (h40810 : (¬ p2027))
    (h9608 : p2027 ∨ (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3425) ∨ (¬ p4777) ∨ (¬ p4917))
    : (¬ p2696) ∨ (¬ p3136) ∨ (¬ p3425) ∨ (¬ p4777) ∨ (¬ p4917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9608 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41108 (p2027 p2696 p2743 p3555 p3589 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h9609 : p2027 ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3555) ∨ (¬ p3589) ∨ (¬ p4377))
    : (¬ p2696) ∨ (¬ p2743) ∨ (¬ p3555) ∨ (¬ p3589) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9609 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41109 (p2027 p2696 p2727 p2742 p3425 p4650 p4777 : Prop)
    (h40810 : (¬ p2027))
    (h9610 : p2027 ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p3425) ∨ (¬ p4650) ∨ (¬ p4777))
    : (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p3425) ∨ (¬ p4650) ∨ (¬ p4777) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4777 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9610 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41110 (p2027 p2132 p2860 p3425 p4169 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9611 : p2027 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4555))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9611 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41111 (p2027 p2341 p2926 p2963 p3487 p3548 p4104 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h9614 : p2027 ∨ (¬ p2341) ∨ (¬ p2926) ∨ (¬ p2963) ∨ (¬ p3487) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4972))
    : (¬ p2341) ∨ (¬ p2926) ∨ (¬ p2963) ∨ (¬ p3487) ∨ (¬ p3548) ∨ (¬ p4104) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2926 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9614 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41112 (p2027 p2930 p3343 p3742 p3817 p4451 : Prop)
    (h40810 : (¬ p2027))
    (h9615 : p2027 ∨ (¬ p2930) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3817) ∨ (¬ p4451))
    : (¬ p2930) ∨ (¬ p3343) ∨ (¬ p3742) ∨ (¬ p3817) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2930 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9615 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41114 (p2027 p3564 p3660 p3744 p4235 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h9617 : p2027 ∨ (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3744) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p3564) ∨ (¬ p3660) ∨ (¬ p3744) ∨ (¬ p4235) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9617 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41115 (p2027 p2563 p3125 p4026 p4512 p4629 : Prop)
    (h40810 : (¬ p2027))
    (h9618 : p2027 ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4629))
    : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p4026) ∨ (¬ p4512) ∨ (¬ p4629) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9618 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41117 (p2027 p2850 p3051 p3486 p4109 p4202 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h9654 : p2027 ∨ (¬ p2850) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p5214))
    : (¬ p2850) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9654 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41118 (p2027 p2331 p2952 p3986 p4173 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h9655 : p2027 ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4173) ∨ (¬ p4957))
    : (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) ∨ (¬ p4173) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9655 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41120 (p2027 p2982 p3690 p4235 p4395 : Prop)
    (h40810 : (¬ p2027))
    (h9657 : p2027 ∨ (¬ p2982) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4395))
    : (¬ p2982) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h9657 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step41121 (p2027 p2138 p2341 p2748 p3031 p3548 p3819 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h9658 : p2027 ∨ (¬ p2138) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p5049))
    : (¬ p2138) ∨ (¬ p2341) ∨ (¬ p2748) ∨ (¬ p3031) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9658 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41122 (p2027 p2264 p3570 p4037 p4140 p4156 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h9676 : p2027 ∨ (¬ p2264) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4140) ∨ (¬ p4156) ∨ (¬ p4620))
    : (¬ p2264) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4140) ∨ (¬ p4156) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9676 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41124 (p2027 p2191 p2341 p2891 p4132 p4990 : Prop)
    (h40810 : (¬ p2027))
    (h9678 : p2027 ∨ (¬ p2191) ∨ (¬ p2341) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4990))
    : (¬ p2191) ∨ (¬ p2341) ∨ (¬ p2891) ∨ (¬ p4132) ∨ (¬ p4990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9678 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41125 (p2027 p2662 p2922 p3540 p3662 p4281 p4701 : Prop)
    (h40810 : (¬ p2027))
    (h9679 : p2027 ∨ (¬ p2662) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701))
    : (¬ p2662) ∨ (¬ p2922) ∨ (¬ p3540) ∨ (¬ p3662) ∨ (¬ p4281) ∨ (¬ p4701) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4701 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9679 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41126 (p2027 p2284 p3238 p3413 p3646 p4031 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9680 : p2027 ∨ (¬ p2284) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4811))
    : (¬ p2284) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9680 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41127 (p2027 p2481 p2509 p3256 p3580 p3857 p4044 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9681 : p2027 ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3580) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4811))
    : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p3256) ∨ (¬ p3580) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9681 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41128 (p2027 p2518 p2928 p4278 p4404 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h9682 : p2027 ∨ (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666))
    : (¬ p2518) ∨ (¬ p2928) ∨ (¬ p4278) ∨ (¬ p4404) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9682 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41129 (p2027 p2088 p2177 p4107 p4445 p4592 : Prop)
    (h40810 : (¬ p2027))
    (h9683 : p2027 ∨ (¬ p2088) ∨ (¬ p2177) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4592))
    : (¬ p2088) ∨ (¬ p2177) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4592) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4592 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9683 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41130 (p2027 p2481 p2509 p2810 p3005 p3171 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9684 : p2027 ∨ (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4811))
    : (¬ p2481) ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9684 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41131 (p2027 p2509 p2657 p3166 p4346 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9685 : p2027 ∨ (¬ p2509) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4346) ∨ (¬ p4811))
    : (¬ p2509) ∨ (¬ p2657) ∨ (¬ p3166) ∨ (¬ p4346) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9685 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41132 (p2027 p2532 p3212 p4120 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h9686 : p2027 ∨ (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2532) ∨ (¬ p3212) ∨ (¬ p4120) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2532 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9686 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41133 (p2027 p2810 p2951 p3136 p3238 p4031 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9687 : p2027 ∨ (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3238) ∨ (¬ p4031) ∨ (¬ p4811))
    : (¬ p2810) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3238) ∨ (¬ p4031) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9687 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41135 (p2027 p2449 p2928 p3580 p3821 p4279 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9689 : p2027 ∨ (¬ p2449) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4811))
    : (¬ p2449) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9689 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41137 (p2027 p2132 p3055 p3238 p3695 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h9691 : p2027 ∨ (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3695) ∨ (¬ p5214))
    : (¬ p2132) ∨ (¬ p3055) ∨ (¬ p3238) ∨ (¬ p3695) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9691 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41138 (p2027 p2307 p3189 p3549 p3567 p4245 p4773 : Prop)
    (h40810 : (¬ p2027))
    (h9692 : p2027 ∨ (¬ p2307) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4773))
    : (¬ p2307) ∨ (¬ p3189) ∨ (¬ p3549) ∨ (¬ p3567) ∨ (¬ p4245) ∨ (¬ p4773) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9692 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41139 (p2027 p2363 p2383 p2781 p2810 p3365 p3693 p4256 p4348 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h9693 : p2027 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h9693 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41140 (p2027 p2363 p3266 p3657 p4381 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h9697 : p2027 ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4503))
    : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9697 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41141 (p2027 p3125 p3461 p4564 p5274 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h9698 : p2027 ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4564) ∨ (¬ p5274) ∨ (¬ p5284))
    : (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4564) ∨ (¬ p5274) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9698 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41143 (p2027 p2274 p3791 p4067 p4391 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h9718 : p2027 ∨ (¬ p2274) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4564))
    : (¬ p2274) ∨ (¬ p3791) ∨ (¬ p4067) ∨ (¬ p4391) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9718 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41145 (p2027 p2579 p3389 p3568 p4710 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h9738 : p2027 ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973))
    : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9738 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41146 (p2027 p2501 p2579 p3389 p3549 p4710 : Prop)
    (h40810 : (¬ p2027))
    (h9739 : p2027 ∨ (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3549) ∨ (¬ p4710))
    : (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3549) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2501 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9739 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41147 (p2027 p2741 p2807 p2811 p2996 p3367 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h9741 : p2027 ∨ (¬ p2741) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2996) ∨ (¬ p3367) ∨ (¬ p4752))
    : (¬ p2741) ∨ (¬ p2807) ∨ (¬ p2811) ∨ (¬ p2996) ∨ (¬ p3367) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2741 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9741 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41148 (p2027 p2761 p3040 p3631 p4429 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h9742 : p2027 ∨ (¬ p2761) ∨ (¬ p3040) ∨ (¬ p3631) ∨ (¬ p4429) ∨ (¬ p5284))
    : (¬ p2761) ∨ (¬ p3040) ∨ (¬ p3631) ∨ (¬ p4429) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9742 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41149 (p2027 p2819 p3367 p3923 p3953 p5221 : Prop)
    (h40810 : (¬ p2027))
    (h9743 : p2027 ∨ (¬ p2819) ∨ (¬ p3367) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5221))
    : (¬ p2819) ∨ (¬ p3367) ∨ (¬ p3923) ∨ (¬ p3953) ∨ (¬ p5221) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9743 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41150 (p2027 p2220 p3646 p3956 p3958 p4441 : Prop)
    (h40810 : (¬ p2027))
    (h9744 : p2027 ∨ (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4441))
    : (¬ p2220) ∨ (¬ p3646) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9744 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41151 (p2027 p2295 p2313 p2386 p2499 p3019 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9745 : p2027 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p3019) ∨ (¬ p4811))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p3019) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9745 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41152 (p2027 p2230 p2284 p2579 p3096 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h9746 : p2027 ∨ (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4705))
    : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2579) ∨ (¬ p3096) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9746 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41153 (p2027 p2499 p2774 p3055 p4390 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h9747 : p2027 ∨ (¬ p2499) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p4390) ∨ (¬ p5214))
    : (¬ p2499) ∨ (¬ p2774) ∨ (¬ p3055) ∨ (¬ p4390) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9747 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41154 (p2027 p2685 p2810 p2928 p3579 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9748 : p2027 ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2928) ∨ (¬ p3579) ∨ (¬ p4811))
    : (¬ p2685) ∨ (¬ p2810) ∨ (¬ p2928) ∨ (¬ p3579) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9748 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41156 (p2027 p2307 p2476 p2584 p2588 p4595 : Prop)
    (h40810 : (¬ p2027))
    (h9750 : p2027 ∨ (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p4595))
    : (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p4595) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9750 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41157 (p2027 p2190 p3146 p3956 p3958 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h9751 : p2027 ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4347))
    : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9751 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41158 (p2027 p2307 p2493 p2586 p2928 p3921 : Prop)
    (h40810 : (¬ p2027))
    (h9752 : p2027 ∨ (¬ p2307) ∨ (¬ p2493) ∨ (¬ p2586) ∨ (¬ p2928) ∨ (¬ p3921))
    : (¬ p2307) ∨ (¬ p2493) ∨ (¬ p2586) ∨ (¬ p2928) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9752 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41160 (p2027 p2318 p2319 p2588 p3125 p3946 p3958 : Prop)
    (h40810 : (¬ p2027))
    (h9755 : p2027 ∨ (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p3958))
    : (¬ p2318) ∨ (¬ p2319) ∨ (¬ p2588) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p3958) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9755 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41161 (p2027 p2318 p2717 p3426 p3549 p3551 p4867 : Prop)
    (h40810 : (¬ p2027))
    (h9756 : p2027 ∨ (¬ p2318) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3549) ∨ (¬ p3551) ∨ (¬ p4867))
    : (¬ p2318) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3549) ∨ (¬ p3551) ∨ (¬ p4867) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9756 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41164 (p2027 p2274 p2284 p2588 p2590 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h9759 : p2027 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4705))
    : (¬ p2274) ∨ (¬ p2284) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9759 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41165 (p2027 p2870 p3549 p3758 p4140 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h9760 : p2027 ∨ (¬ p2870) ∨ (¬ p3549) ∨ (¬ p3758) ∨ (¬ p4140) ∨ (¬ p4514))
    : (¬ p2870) ∨ (¬ p3549) ∨ (¬ p3758) ∨ (¬ p4140) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9760 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41166 (p2027 p2307 p3549 p3954 p4512 p4877 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h9762 : p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5020))
    : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4512) ∨ (¬ p4877) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9762 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41167 (p2027 p2284 p2307 p2504 p2590 p3549 p3743 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h9763 : p2027 ∨ (¬ p2284) ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4705))
    : (¬ p2284) ∨ (¬ p2307) ∨ (¬ p2504) ∨ (¬ p2590) ∨ (¬ p3549) ∨ (¬ p3743) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2504 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9763 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41168 (p2027 p2307 p2584 p2656 p2992 p3549 p4245 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h9765 : p2027 ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4704))
    : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2656) ∨ (¬ p2992) ∨ (¬ p3549) ∨ (¬ p4245) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9765 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41169 (p2027 p2307 p2584 p2630 p2656 p2745 p3549 p4245 : Prop)
    (h40810 : (¬ p2027))
    (h9766 : p2027 ∨ (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3549) ∨ (¬ p4245))
    : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3549) ∨ (¬ p4245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9766 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41172 (p2027 p2307 p2373 p2588 p2590 p3743 p4509 : Prop)
    (h40810 : (¬ p2027))
    (h9769 : p2027 ∨ (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4509))
    : (¬ p2307) ∨ (¬ p2373) ∨ (¬ p2588) ∨ (¬ p2590) ∨ (¬ p3743) ∨ (¬ p4509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9769 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41174 (p2027 p3097 p3309 p4110 p4338 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h9771 : p2027 ∨ (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4110) ∨ (¬ p4338) ∨ (¬ p4632))
    : (¬ p3097) ∨ (¬ p3309) ∨ (¬ p4110) ∨ (¬ p4338) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9771 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41175 (p2027 p2507 p2588 p3399 p3547 p3591 : Prop)
    (h40810 : (¬ p2027))
    (h9773 : p2027 ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591))
    : (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3399) ∨ (¬ p3547) ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2507 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9773 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41176 (p2027 p2928 p3389 p3954 p4079 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h9775 : p2027 ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216))
    : (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3954) ∨ (¬ p4079) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2928 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9775 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41177 (p2027 p2166 p3956 p3958 p4173 p4441 : Prop)
    (h40810 : (¬ p2027))
    (h9776 : p2027 ∨ (¬ p2166) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4173) ∨ (¬ p4441))
    : (¬ p2166) ∨ (¬ p3956) ∨ (¬ p3958) ∨ (¬ p4173) ∨ (¬ p4441) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9776 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41179 (p2027 p2588 p2891 p3958 p4140 p4173 : Prop)
    (h40810 : (¬ p2027))
    (h9778 : p2027 ∨ (¬ p2588) ∨ (¬ p2891) ∨ (¬ p3958) ∨ (¬ p4140) ∨ (¬ p4173))
    : (¬ p2588) ∨ (¬ p2891) ∨ (¬ p3958) ∨ (¬ p4140) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9778 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41180 (p2027 p2963 p3166 p3956 p4417 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h9780 : p2027 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3956) ∨ (¬ p4417) ∨ (¬ p4976))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3956) ∨ (¬ p4417) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9780 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41181 (p2027 p2387 p3654 p3692 p4345 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h9781 : p2027 ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433))
    : (¬ p2387) ∨ (¬ p3654) ∨ (¬ p3692) ∨ (¬ p4345) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9781 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41183 (p2027 p2383 p2901 p3324 p3743 p4153 p4558 : Prop)
    (h40810 : (¬ p2027))
    (h9783 : p2027 ∨ (¬ p2383) ∨ (¬ p2901) ∨ (¬ p3324) ∨ (¬ p3743) ∨ (¬ p4153) ∨ (¬ p4558))
    : (¬ p2383) ∨ (¬ p2901) ∨ (¬ p3324) ∨ (¬ p3743) ∨ (¬ p4153) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4153 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9783 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41184 (p2027 p2946 p3146 p3156 p3201 p3540 p3905 p4697 p4786 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h9786 : p2027 ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160))
    : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3201) ∨ (¬ p3540) ∨ (¬ p3905) ∨ (¬ p4697) ∨ (¬ p4786) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h9786 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41185 (p2027 p2933 p3399 p3452 p3742 p4814 : Prop)
    (h40810 : (¬ p2027))
    (h9787 : p2027 ∨ (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4814))
    : (¬ p2933) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3742) ∨ (¬ p4814) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2933 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9787 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41186 (p2027 p2247 p2744 p2928 p3389 p4079 p4257 : Prop)
    (h40810 : (¬ p2027))
    (h9788 : p2027 ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4257))
    : (¬ p2247) ∨ (¬ p2744) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4079) ∨ (¬ p4257) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9788 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41187 (p2027 p2946 p3055 p3146 p3156 p3876 p4278 p4669 p4786 : Prop)
    (h40810 : (¬ p2027))
    (h9823 : p2027 ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786))
    : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h9823 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41188 (p2027 p3471 p3555 p3588 p3589 p4377 : Prop)
    (h40810 : (¬ p2027))
    (h9825 : p2027 ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p3588) ∨ (¬ p3589) ∨ (¬ p4377))
    : (¬ p3471) ∨ (¬ p3555) ∨ (¬ p3588) ∨ (¬ p3589) ∨ (¬ p4377) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3471 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9825 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41189 (p2027 p2922 p3541 p3583 p3876 p4881 : Prop)
    (h40810 : (¬ p2027))
    (h9826 : p2027 ∨ (¬ p2922) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3876) ∨ (¬ p4881))
    : (¬ p2922) ∨ (¬ p3541) ∨ (¬ p3583) ∨ (¬ p3876) ∨ (¬ p4881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9826 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41190 (p2027 p3379 p3583 p3954 p4030 p4881 : Prop)
    (h40810 : (¬ p2027))
    (h9827 : p2027 ∨ (¬ p3379) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4881))
    : (¬ p3379) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p4881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9827 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41191 (p2027 p2743 p3631 p3687 p4324 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h9828 : p2027 ∨ (¬ p2743) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p4324) ∨ (¬ p4782))
    : (¬ p2743) ∨ (¬ p3631) ∨ (¬ p3687) ∨ (¬ p4324) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9828 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41192 (p2027 p2761 p3434 p4025 p4191 p4477 : Prop)
    (h40810 : (¬ p2027))
    (h9830 : p2027 ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4477))
    : (¬ p2761) ∨ (¬ p3434) ∨ (¬ p4025) ∨ (¬ p4191) ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4025 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9830 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41194 (p2027 p2383 p2437 p2962 p3324 p4109 p4194 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h9832 : p2027 ∨ (¬ p2383) ∨ (¬ p2437) ∨ (¬ p2962) ∨ (¬ p3324) ∨ (¬ p4109) ∨ (¬ p4194) ∨ (¬ p4646))
    : (¬ p2383) ∨ (¬ p2437) ∨ (¬ p2962) ∨ (¬ p3324) ∨ (¬ p4109) ∨ (¬ p4194) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9832 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41195 (p2027 p2246 p2744 p2761 p2946 p3146 p3156 p3366 p3425 p4669 p5228 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h9833 : p2027 ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4669) ∨ (¬ p5228) ∨ (¬ p5387))
    : (¬ p2246) ∨ (¬ p2744) ∨ (¬ p2761) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3366) ∨ (¬ p3425) ∨ (¬ p4669) ∨ (¬ p5228) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : (¬ p2027) := h40810;
    (Or.elim h9833 (fun q0 => (False.elim (u11 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u9))) (fun r10 => (False.elim (r10 u10)))))))))))))))))))))))))

theorem step41196 (p2027 p2664 p2946 p3156 p3540 p3658 p3969 p4324 p4381 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h9834 : p2027 ∨ (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5119))
    : (¬ p2664) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3540) ∨ (¬ p3658) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2664 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h9834 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41197 (p2027 p2274 p3461 p4205 p4322 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h9854 : p2027 ∨ (¬ p2274) ∨ (¬ p3461) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4620))
    : (¬ p2274) ∨ (¬ p3461) ∨ (¬ p4205) ∨ (¬ p4322) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4205 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9854 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41198 (p2027 p2246 p2608 p2744 p2946 p3146 p3156 p3817 p4366 p4669 : Prop)
    (h40810 : (¬ p2027))
    (h9855 : p2027 ∨ (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669))
    : (¬ p2246) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h9855 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step41199 (p2027 p2098 p2247 p2744 p3589 p4242 : Prop)
    (h40810 : (¬ p2027))
    (h9856 : p2027 ∨ (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3589) ∨ (¬ p4242))
    : (¬ p2098) ∨ (¬ p2247) ∨ (¬ p2744) ∨ (¬ p3589) ∨ (¬ p4242) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9856 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41200 (p2027 p2743 p3399 p3576 p3954 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h9857 : p2027 ∨ (¬ p2743) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3954) ∨ (¬ p4782))
    : (¬ p2743) ∨ (¬ p3399) ∨ (¬ p3576) ∨ (¬ p3954) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9857 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41201 (p2027 p2743 p3093 p3954 p4024 p4845 : Prop)
    (h40810 : (¬ p2027))
    (h9858 : p2027 ∨ (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4845))
    : (¬ p2743) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p4024) ∨ (¬ p4845) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4845 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41202 (p2027 p2946 p3156 p3425 p3969 p4324 p4381 p4786 p5119 : Prop)
    (h40810 : (¬ p2027))
    (h9859 : p2027 ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5119))
    : (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3425) ∨ (¬ p3969) ∨ (¬ p4324) ∨ (¬ p4381) ∨ (¬ p4786) ∨ (¬ p5119) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h9859 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41203 (p2027 p2911 p3362 p3389 p3551 p5260 : Prop)
    (h40810 : (¬ p2027))
    (h9897 : p2027 ∨ (¬ p2911) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3551) ∨ (¬ p5260))
    : (¬ p2911) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3551) ∨ (¬ p5260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9897 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41204 (p2027 p2534 p3516 p3551 p4420 p4443 : Prop)
    (h40810 : (¬ p2027))
    (h9898 : p2027 ∨ (¬ p2534) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4420) ∨ (¬ p4443))
    : (¬ p2534) ∨ (¬ p3516) ∨ (¬ p3551) ∨ (¬ p4420) ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9898 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41205 (p2027 p2387 p3654 p4118 p4345 p4771 : Prop)
    (h40810 : (¬ p2027))
    (h9900 : p2027 ∨ (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4118) ∨ (¬ p4345) ∨ (¬ p4771))
    : (¬ p2387) ∨ (¬ p3654) ∨ (¬ p4118) ∨ (¬ p4345) ∨ (¬ p4771) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9900 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41208 (p2027 p2584 p2589 p2667 p3027 p3579 p4154 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h9904 : p2027 ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p3027) ∨ (¬ p3579) ∨ (¬ p4154) ∨ (¬ p4646))
    : (¬ p2584) ∨ (¬ p2589) ∨ (¬ p2667) ∨ (¬ p3027) ∨ (¬ p3579) ∨ (¬ p4154) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2584 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h9904 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41209 (p2027 p2589 p2707 p3363 p3585 p3658 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h9905 : p2027 ∨ (¬ p2589) ∨ (¬ p2707) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4646))
    : (¬ p2589) ∨ (¬ p2707) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9905 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41210 (p2027 p3670 p3692 p4444 p4746 p5344 : Prop)
    (h40810 : (¬ p2027))
    (h9907 : p2027 ∨ (¬ p3670) ∨ (¬ p3692) ∨ (¬ p4444) ∨ (¬ p4746) ∨ (¬ p5344))
    : (¬ p3670) ∨ (¬ p3692) ∨ (¬ p4444) ∨ (¬ p4746) ∨ (¬ p5344) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9907 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41211 (p2027 p2363 p2373 p3949 p4433 p4948 : Prop)
    (h40810 : (¬ p2027))
    (h9908 : p2027 ∨ (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3949) ∨ (¬ p4433) ∨ (¬ p4948))
    : (¬ p2363) ∨ (¬ p2373) ∨ (¬ p3949) ∨ (¬ p4433) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9908 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41212 (p2027 p3599 p3692 p4242 p4746 p5343 : Prop)
    (h40810 : (¬ p2027))
    (h9909 : p2027 ∨ (¬ p3599) ∨ (¬ p3692) ∨ (¬ p4242) ∨ (¬ p4746) ∨ (¬ p5343))
    : (¬ p3599) ∨ (¬ p3692) ∨ (¬ p4242) ∨ (¬ p4746) ∨ (¬ p5343) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9909 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41213 (p2027 p2132 p3583 p3589 p4366 p4793 : Prop)
    (h40810 : (¬ p2027))
    (h9910 : p2027 ∨ (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793))
    : (¬ p2132) ∨ (¬ p3583) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9910 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41214 (p2027 p2088 p2112 p3537 p4379 p5339 : Prop)
    (h40810 : (¬ p2027))
    (h9911 : p2027 ∨ (¬ p2088) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p4379) ∨ (¬ p5339))
    : (¬ p2088) ∨ (¬ p2112) ∨ (¬ p3537) ∨ (¬ p4379) ∨ (¬ p5339) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5339 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9911 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41216 (p2027 p2313 p3654 p4276 p4278 p4623 : Prop)
    (h40810 : (¬ p2027))
    (h9913 : p2027 ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623))
    : (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4276) ∨ (¬ p4278) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9913 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41217 (p2027 p2972 p3958 p4137 p4173 p5045 : Prop)
    (h40810 : (¬ p2027))
    (h9915 : p2027 ∨ (¬ p2972) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4173) ∨ (¬ p5045))
    : (¬ p2972) ∨ (¬ p3958) ∨ (¬ p4137) ∨ (¬ p4173) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9915 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41218 (p2027 p2230 p2563 p3369 p3646 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h9916 : p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3369) ∨ (¬ p3646) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9916 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41219 (p2027 p2307 p2588 p2962 p4032 p4203 p5043 : Prop)
    (h40810 : (¬ p2027))
    (h9917 : p2027 ∨ (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2962) ∨ (¬ p4032) ∨ (¬ p4203) ∨ (¬ p5043))
    : (¬ p2307) ∨ (¬ p2588) ∨ (¬ p2962) ∨ (¬ p4032) ∨ (¬ p4203) ∨ (¬ p5043) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5043 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9917 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41220 (p2027 p2318 p2507 p2588 p3527 p3551 p4452 : Prop)
    (h40810 : (¬ p2027))
    (h9919 : p2027 ∨ (¬ p2318) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4452))
    : (¬ p2318) ∨ (¬ p2507) ∨ (¬ p2588) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p4452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2318 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9919 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41221 (p2027 p2619 p2810 p2957 p4120 p4313 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h9920 : p2027 ∨ (¬ p2619) ∨ (¬ p2810) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2619) ∨ (¬ p2810) ∨ (¬ p2957) ∨ (¬ p4120) ∨ (¬ p4313) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9920 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41224 (p2027 p2191 p2563 p2668 p4210 p4506 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h9925 : p2027 ∨ (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p4210) ∨ (¬ p4506) ∨ (¬ p4560))
    : (¬ p2191) ∨ (¬ p2563) ∨ (¬ p2668) ∨ (¬ p4210) ∨ (¬ p4506) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9925 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41228 (p2027 p2743 p3707 p5333 p5387 p5460 : Prop)
    (h40810 : (¬ p2027))
    (h9929 : p2027 ∨ (¬ p2743) ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p5387) ∨ (¬ p5460))
    : (¬ p2743) ∨ (¬ p3707) ∨ (¬ p5333) ∨ (¬ p5387) ∨ (¬ p5460) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5460 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9929 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41229 (p2027 p2641 p3497 p3662 p3984 p4203 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h9930 : p2027 ∨ (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3984) ∨ (¬ p4203) ∨ (¬ p4507))
    : (¬ p2641) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p3984) ∨ (¬ p4203) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9930 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41230 (p2027 p2191 p2373 p2922 p4202 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h9931 : p2027 ∨ (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2922) ∨ (¬ p4202) ∨ (¬ p4646))
    : (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2922) ∨ (¬ p4202) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9931 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41231 (p2027 p3609 p3857 p3923 p4113 p4861 p4867 : Prop)
    (h40810 : (¬ p2027))
    (h9932 : p2027 ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3923) ∨ (¬ p4113) ∨ (¬ p4861) ∨ (¬ p4867))
    : (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3923) ∨ (¬ p4113) ∨ (¬ p4861) ∨ (¬ p4867) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4113 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4861 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4867 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9932 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41232 (p2027 p2191 p2220 p2745 p2951 p3136 p3368 : Prop)
    (h40810 : (¬ p2027))
    (h9934 : p2027 ∨ (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3368))
    : (¬ p2191) ∨ (¬ p2220) ∨ (¬ p2745) ∨ (¬ p2951) ∨ (¬ p3136) ∨ (¬ p3368) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9934 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41234 (p2027 p3063 p3146 p4026 p4134 p4171 : Prop)
    (h40810 : (¬ p2027))
    (h9940 : p2027 ∨ (¬ p3063) ∨ (¬ p3146) ∨ (¬ p4026) ∨ (¬ p4134) ∨ (¬ p4171))
    : (¬ p3063) ∨ (¬ p3146) ∨ (¬ p4026) ∨ (¬ p4134) ∨ (¬ p4171) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9940 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41239 (p2027 p2241 p2254 p3027 p3172 p4044 : Prop)
    (h40810 : (¬ p2027))
    (h9945 : p2027 ∨ (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3172) ∨ (¬ p4044))
    : (¬ p2241) ∨ (¬ p2254) ∨ (¬ p3027) ∨ (¬ p3172) ∨ (¬ p4044) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9945 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41240 (p2027 p2230 p2656 p3027 p3238 p3402 p4652 : Prop)
    (h40810 : (¬ p2027))
    (h9946 : p2027 ∨ (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4652))
    : (¬ p2230) ∨ (¬ p2656) ∨ (¬ p3027) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p4652) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9946 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41241 (p2027 p2138 p2331 p4117 p4195 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h9947 : p2027 ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p5049))
    : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p4117) ∨ (¬ p4195) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9947 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41242 (p2027 p2696 p2797 p3055 p4343 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h9948 : p2027 ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p4975))
    : (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3055) ∨ (¬ p4343) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9948 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41243 (p2027 p2254 p2459 p2952 p3399 p3527 p3744 p3952 p4604 : Prop)
    (h40810 : (¬ p2027))
    (h9949 : p2027 ∨ (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604))
    : (¬ p2254) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h9949 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41244 (p2027 p2470 p3540 p3570 p4370 p4647 p5307 : Prop)
    (h40810 : (¬ p2027))
    (h9950 : p2027 ∨ (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4370) ∨ (¬ p4647) ∨ (¬ p5307))
    : (¬ p2470) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4370) ∨ (¬ p4647) ∨ (¬ p5307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9950 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41245 (p2027 p2274 p2312 p3516 p3947 p4067 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h9951 : p2027 ∨ (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4564))
    : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9951 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41246 (p2027 p2299 p2319 p3527 p3546 p3946 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h9952 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3946) ∨ (¬ p4620))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p3527) ∨ (¬ p3546) ∨ (¬ p3946) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3546 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9952 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41247 (p2027 p2619 p3690 p4042 p4244 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h9953 : p2027 ∨ (¬ p2619) ∨ (¬ p3690) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4666))
    : (¬ p2619) ∨ (¬ p3690) ∨ (¬ p4042) ∨ (¬ p4244) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9953 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41248 (p2027 p2449 p3097 p3547 p3817 p4156 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h9990 : p2027 ∨ (¬ p2449) ∨ (¬ p3097) ∨ (¬ p3547) ∨ (¬ p3817) ∨ (¬ p4156) ∨ (¬ p4560))
    : (¬ p2449) ∨ (¬ p3097) ∨ (¬ p3547) ∨ (¬ p3817) ∨ (¬ p4156) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9990 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41249 (p2027 p2386 p2499 p2797 p2810 p3567 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h9991 : p2027 ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4811))
    : (¬ p2386) ∨ (¬ p2499) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3567) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h9991 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41250 (p2027 p2807 p2963 p3097 p3552 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h9993 : p2027 ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560))
    : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9993 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41251 (p2027 p2254 p2952 p3073 p3449 p3952 p3989 p4348 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h9994 : p2027 ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503))
    : (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3952) ∨ (¬ p3989) ∨ (¬ p4348) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2254 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h9994 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step41252 (p2027 p3367 p3609 p4261 p4436 p5370 : Prop)
    (h40810 : (¬ p2027))
    (h9995 : p2027 ∨ (¬ p3367) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p4436) ∨ (¬ p5370))
    : (¬ p3367) ∨ (¬ p3609) ∨ (¬ p4261) ∨ (¬ p4436) ∨ (¬ p5370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4436 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9995 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41253 (p2027 p2363 p3325 p3553 p4348 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h9996 : p2027 ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4570))
    : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h9996 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41256 (p2027 p3063 p3791 p4105 p4405 p4442 : Prop)
    (h40810 : (¬ p2027))
    (h10016 : p2027 ∨ (¬ p3063) ∨ (¬ p3791) ∨ (¬ p4105) ∨ (¬ p4405) ∨ (¬ p4442))
    : (¬ p3063) ∨ (¬ p3791) ∨ (¬ p4105) ∨ (¬ p4405) ∨ (¬ p4442) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10016 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41258 (p2027 p2860 p3246 p3576 p3817 p4136 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10018 : p2027 ∨ (¬ p2860) ∨ (¬ p3246) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4136) ∨ (¬ p4555))
    : (¬ p2860) ∨ (¬ p3246) ∨ (¬ p3576) ∨ (¬ p3817) ∨ (¬ p4136) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3576 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10018 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41259 (p2027 p2881 p3051 p4032 p4382 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h10019 : p2027 ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4666))
    : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p4032) ∨ (¬ p4382) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10019 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41260 (p2027 p2498 p3063 p3660 p3989 p4235 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10020 : p2027 ∨ (¬ p2498) ∨ (¬ p3063) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p2498) ∨ (¬ p3063) ∨ (¬ p3660) ∨ (¬ p3989) ∨ (¬ p4235) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2498 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10020 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41262 (p2027 p2122 p2313 p2386 p2499 p4375 p5214 : Prop)
    (h40810 : (¬ p2027))
    (h10023 : p2027 ∨ (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p4375) ∨ (¬ p5214))
    : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p4375) ∨ (¬ p5214) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2499 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5214 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10023 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41263 (p2027 p2284 p3246 p3947 p4386 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h10024 : p2027 ∨ (¬ p2284) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4555))
    : (¬ p2284) ∨ (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10024 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41264 (p2027 p2727 p2996 p3201 p3740 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h10025 : p2027 ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3201) ∨ (¬ p3740) ∨ (¬ p4753))
    : (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3201) ∨ (¬ p3740) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10025 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41265 (p2027 p3005 p3568 p4195 p4405 p4417 : Prop)
    (h40810 : (¬ p2027))
    (h10026 : p2027 ∨ (¬ p3005) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4417))
    : (¬ p3005) ∨ (¬ p3568) ∨ (¬ p4195) ∨ (¬ p4405) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10026 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41268 (p2027 p2797 p3323 p3946 p3983 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h10029 : p2027 ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p3983) ∨ (¬ p4787))
    : (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3946) ∨ (¬ p3983) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10029 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41269 (p2027 p2295 p2312 p2493 p2928 p4279 p4976 : Prop)
    (h40810 : (¬ p2027))
    (h10032 : p2027 ∨ (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p4279) ∨ (¬ p4976))
    : (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2493) ∨ (¬ p2928) ∨ (¬ p4279) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2928 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10032 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41270 (p2027 p2387 p2667 p2745 p2819 p4154 p4426 : Prop)
    (h40810 : (¬ p2027))
    (h10033 : p2027 ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2819) ∨ (¬ p4154) ∨ (¬ p4426))
    : (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2819) ∨ (¬ p4154) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10033 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41271 (p2027 p2534 p3256 p3574 p4121 p4598 : Prop)
    (h40810 : (¬ p2027))
    (h10055 : p2027 ∨ (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4121) ∨ (¬ p4598))
    : (¬ p2534) ∨ (¬ p3256) ∨ (¬ p3574) ∨ (¬ p4121) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10055 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41273 (p2027 p2396 p2819 p3689 p4324 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10057 : p2027 ∨ (¬ p2396) ∨ (¬ p2819) ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p4405))
    : (¬ p2396) ∨ (¬ p2819) ∨ (¬ p3689) ∨ (¬ p4324) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3689 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41275 (p2027 p2992 p3574 p4111 p4241 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h10059 : p2027 ∨ (¬ p2992) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4715))
    : (¬ p2992) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10059 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41276 (p2027 p2098 p3425 p3570 p4804 p4898 : Prop)
    (h40810 : (¬ p2027))
    (h10060 : p2027 ∨ (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4804) ∨ (¬ p4898))
    : (¬ p2098) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4804) ∨ (¬ p4898) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10060 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41279 (p2027 p2299 p3166 p3414 p4361 p4378 : Prop)
    (h40810 : (¬ p2027))
    (h10063 : p2027 ∨ (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p4361) ∨ (¬ p4378))
    : (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p4361) ∨ (¬ p4378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10063 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41280 (p2027 p2946 p3055 p4117 p4315 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h10064 : p2027 ∨ (¬ p2946) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4749))
    : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p4117) ∨ (¬ p4315) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10064 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41281 (p2027 p2299 p3166 p3414 p3699 p4378 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10065 : p2027 ∨ (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4378) ∨ (¬ p4559))
    : (¬ p2299) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4378) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10065 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41282 (p2027 p2696 p2727 p2742 p2780 p4337 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h10066 : p2027 ∨ (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2780) ∨ (¬ p4337) ∨ (¬ p4972))
    : (¬ p2696) ∨ (¬ p2727) ∨ (¬ p2742) ∨ (¬ p2780) ∨ (¬ p4337) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10066 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41283 (p2027 p2132 p2745 p3365 p3662 p5051 : Prop)
    (h40810 : (¬ p2027))
    (h10067 : p2027 ∨ (¬ p2132) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p5051))
    : (¬ p2132) ∨ (¬ p2745) ∨ (¬ p3365) ∨ (¬ p3662) ∨ (¬ p5051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10067 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41285 (p2027 p2982 p4040 p4107 p4235 p4559 p4660 : Prop)
    (h40810 : (¬ p2027))
    (h10072 : p2027 ∨ (¬ p2982) ∨ (¬ p4040) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4660))
    : (¬ p2982) ∨ (¬ p4040) ∨ (¬ p4107) ∨ (¬ p4235) ∨ (¬ p4559) ∨ (¬ p4660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10072 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41286 (p2027 p3588 p3599 p4107 p4477 p5233 : Prop)
    (h40810 : (¬ p2027))
    (h10073 : p2027 ∨ (¬ p3588) ∨ (¬ p3599) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5233))
    : (¬ p3588) ∨ (¬ p3599) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5233) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10073 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41287 (p2027 p2098 p2299 p3425 p4169 p4559 p4804 : Prop)
    (h40810 : (¬ p2027))
    (h10074 : p2027 ∨ (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804))
    : (¬ p2098) ∨ (¬ p2299) ∨ (¬ p3425) ∨ (¬ p4169) ∨ (¬ p4559) ∨ (¬ p4804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4804 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10074 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41288 (p2027 p2589 p2891 p3948 p4235 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h10076 : p2027 ∨ (¬ p2589) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5191))
    : (¬ p2589) ∨ (¬ p2891) ∨ (¬ p3948) ∨ (¬ p4235) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10076 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41289 (p2027 p2406 p2589 p2662 p2996 p4281 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h10077 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p4281) ∨ (¬ p4650))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2996) ∨ (¬ p4281) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4281 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10077 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41290 (p2027 p2406 p2589 p2743 p3363 p3541 p4752 : Prop)
    (h40810 : (¬ p2027))
    (h10078 : p2027 ∨ (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2743) ∨ (¬ p3363) ∨ (¬ p3541) ∨ (¬ p4752))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2743) ∨ (¬ p3363) ∨ (¬ p3541) ∨ (¬ p4752) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3541 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4752 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10078 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41291 (p2027 p2253 p2651 p2741 p3591 p4111 p4866 : Prop)
    (h40810 : (¬ p2027))
    (h10079 : p2027 ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p3591) ∨ (¬ p4111) ∨ (¬ p4866))
    : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p3591) ∨ (¬ p4111) ∨ (¬ p4866) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10079 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41292 (p2027 p2528 p3266 p3657 p4381 p4438 : Prop)
    (h40810 : (¬ p2027))
    (h10080 : p2027 ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4438))
    : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4381) ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10080 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41294 (p2027 p2737 p2850 p3238 p4257 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h10083 : p2027 ∨ (¬ p2737) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p2737) ∨ (¬ p2850) ∨ (¬ p3238) ∨ (¬ p4257) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10083 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41297 (p2027 p2501 p3276 p4026 p4191 p4422 : Prop)
    (h40810 : (¬ p2027))
    (h10086 : p2027 ∨ (¬ p2501) ∨ (¬ p3276) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p4422))
    : (¬ p2501) ∨ (¬ p3276) ∨ (¬ p4026) ∨ (¬ p4191) ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2501 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10086 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41298 (p2027 p2352 p2406 p2497 p3923 p4715 : Prop)
    (h40810 : (¬ p2027))
    (h10087 : p2027 ∨ (¬ p2352) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p3923) ∨ (¬ p4715))
    : (¬ p2352) ∨ (¬ p2406) ∨ (¬ p2497) ∨ (¬ p3923) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10087 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41299 (p2027 p2427 p2946 p3414 p3699 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10088 : p2027 ∨ (¬ p2427) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4702))
    : (¬ p2427) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3699) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3699 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10088 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41300 (p2027 p2807 p2963 p3549 p3552 p4757 : Prop)
    (h40810 : (¬ p2027))
    (h10089 : p2027 ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3552) ∨ (¬ p4757))
    : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3549) ∨ (¬ p3552) ∨ (¬ p4757) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4757 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10089 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41301 (p2027 p2192 p3136 p3745 p4195 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10090 : p2027 ∨ (¬ p2192) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4960))
    : (¬ p2192) ∨ (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10090 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41302 (p2027 p2717 p2745 p2996 p3551 p4155 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h10091 : p2027 ∨ (¬ p2717) ∨ (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4781))
    : (¬ p2717) ∨ (¬ p2745) ∨ (¬ p2996) ∨ (¬ p3551) ∨ (¬ p4155) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10091 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41303 (p2027 p2191 p2952 p3166 p4311 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h10092 : p2027 ∨ (¬ p2191) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4957))
    : (¬ p2191) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p4311) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10092 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41304 (p2027 p2662 p2745 p3201 p3475 p3540 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h10095 : p2027 ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p3540) ∨ (¬ p4111))
    : (¬ p2662) ∨ (¬ p2745) ∨ (¬ p3201) ∨ (¬ p3475) ∨ (¬ p3540) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10095 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41306 (p2027 p2963 p3166 p3989 p4318 p4560 p5074 : Prop)
    (h40810 : (¬ p2027))
    (h10097 : p2027 ∨ (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p4318) ∨ (¬ p4560) ∨ (¬ p5074))
    : (¬ p2963) ∨ (¬ p3166) ∨ (¬ p3989) ∨ (¬ p4318) ∨ (¬ p4560) ∨ (¬ p5074) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4318 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5074 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10097 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41307 (p2027 p3276 p3917 p4191 p4422 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h10098 : p2027 ∨ (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p5222))
    : (¬ p3276) ∨ (¬ p3917) ∨ (¬ p4191) ∨ (¬ p4422) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10098 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41308 (p2027 p2088 p3266 p3322 p4191 p4617 : Prop)
    (h40810 : (¬ p2027))
    (h10099 : p2027 ∨ (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4617))
    : (¬ p2088) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p4191) ∨ (¬ p4617) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4617 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10099 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41309 (p2027 p2459 p3266 p4802 p5338 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h10100 : p2027 ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4802) ∨ (¬ p5338) ∨ (¬ p5387))
    : (¬ p2459) ∨ (¬ p3266) ∨ (¬ p4802) ∨ (¬ p5338) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4802 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10100 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41310 (p2027 p2417 p3644 p4133 p4347 p4443 : Prop)
    (h40810 : (¬ p2027))
    (h10101 : p2027 ∨ (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443))
    : (¬ p2417) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10101 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41311 (p2027 p2745 p3609 p4118 p4360 p4373 : Prop)
    (h40810 : (¬ p2027))
    (h10102 : p2027 ∨ (¬ p2745) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4373))
    : (¬ p2745) ∨ (¬ p3609) ∨ (¬ p4118) ∨ (¬ p4360) ∨ (¬ p4373) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10102 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41312 (p2027 p2363 p2518 p2531 p3193 p4433 p4440 : Prop)
    (h40810 : (¬ p2027))
    (h10103 : p2027 ∨ (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3193) ∨ (¬ p4433) ∨ (¬ p4440))
    : (¬ p2363) ∨ (¬ p2518) ∨ (¬ p2531) ∨ (¬ p3193) ∨ (¬ p4433) ∨ (¬ p4440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10103 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41313 (p2027 p2589 p3233 p3347 p3707 p4425 p4953 : Prop)
    (h40810 : (¬ p2027))
    (h10104 : p2027 ∨ (¬ p2589) ∨ (¬ p3233) ∨ (¬ p3347) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p4953))
    : (¬ p2589) ∨ (¬ p3233) ∨ (¬ p3347) ∨ (¬ p3707) ∨ (¬ p4425) ∨ (¬ p4953) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10104 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41314 (p2027 p2608 p2737 p4366 p4424 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h10105 : p2027 ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4778))
    : (¬ p2608) ∨ (¬ p2737) ∨ (¬ p4366) ∨ (¬ p4424) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4424 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10105 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41315 (p2027 p2396 p3027 p3297 p3848 p4570 p5295 : Prop)
    (h40810 : (¬ p2027))
    (h10106 : p2027 ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3297) ∨ (¬ p3848) ∨ (¬ p4570) ∨ (¬ p5295))
    : (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3297) ∨ (¬ p3848) ∨ (¬ p4570) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10106 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41316 (p2027 p2252 p2396 p3027 p3292 p4570 p4656 : Prop)
    (h40810 : (¬ p2027))
    (h10107 : p2027 ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3292) ∨ (¬ p4570) ∨ (¬ p4656))
    : (¬ p2252) ∨ (¬ p2396) ∨ (¬ p3027) ∨ (¬ p3292) ∨ (¬ p4570) ∨ (¬ p4656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2252 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10107 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41317 (p2027 p2241 p2992 p3452 p4116 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10108 : p2027 ∨ (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4704))
    : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10108 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41319 (p2027 p2352 p2363 p3692 p3988 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10110 : p2027 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4718))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10110 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41320 (p2027 p2191 p2192 p2352 p4506 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10111 : p2027 ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2352) ∨ (¬ p4506) ∨ (¬ p4718))
    : (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2352) ∨ (¬ p4506) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10111 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41321 (p2027 p2396 p2553 p3690 p4204 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10112 : p2027 ∨ (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4718))
    : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p3690) ∨ (¬ p4204) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10112 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41322 (p2027 p2406 p2474 p2528 p3347 p3857 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h10113 : p2027 ∨ (¬ p2406) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p3347) ∨ (¬ p3857) ∨ (¬ p4608))
    : (¬ p2406) ∨ (¬ p2474) ∨ (¬ p2528) ∨ (¬ p3347) ∨ (¬ p3857) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10113 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41323 (p2027 p2518 p3146 p3193 p4158 p4440 : Prop)
    (h40810 : (¬ p2027))
    (h10115 : p2027 ∨ (¬ p2518) ∨ (¬ p3146) ∨ (¬ p3193) ∨ (¬ p4158) ∨ (¬ p4440))
    : (¬ p2518) ∨ (¬ p3146) ∨ (¬ p3193) ∨ (¬ p4158) ∨ (¬ p4440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2518 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10115 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41324 (p2027 p3146 p3857 p3961 p4063 p4132 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h10116 : p2027 ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4063) ∨ (¬ p4132) ∨ (¬ p5564))
    : (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4063) ∨ (¬ p4132) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10116 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41325 (p2027 p2299 p3146 p3747 p4348 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10134 : p2027 ∨ (¬ p2299) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4559))
    : (¬ p2299) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10134 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41326 (p2027 p2579 p3389 p4137 p4620 p4710 : Prop)
    (h40810 : (¬ p2027))
    (h10135 : p2027 ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710))
    : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10135 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41327 (p2027 p2299 p3747 p3969 p4559 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h10136 : p2027 ∨ (¬ p2299) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4559) ∨ (¬ p5558))
    : (¬ p2299) ∨ (¬ p3747) ∨ (¬ p3969) ∨ (¬ p4559) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10136 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41328 (p2027 p2881 p3941 p3955 p4559 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h10137 : p2027 ∨ (¬ p2881) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p4559) ∨ (¬ p5580))
    : (¬ p2881) ∨ (¬ p3941) ∨ (¬ p3955) ∨ (¬ p4559) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10137 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41329 (p2027 p2104 p2881 p3471 p4800 p4895 : Prop)
    (h40810 : (¬ p2027))
    (h10138 : p2027 ∨ (¬ p2104) ∨ (¬ p2881) ∨ (¬ p3471) ∨ (¬ p4800) ∨ (¬ p4895))
    : (¬ p2104) ∨ (¬ p2881) ∨ (¬ p3471) ∨ (¬ p4800) ∨ (¬ p4895) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4800 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4895 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10138 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41330 (p2027 p3212 p3556 p4107 p4135 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10139 : p2027 ∨ (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4107) ∨ (¬ p4135) ∨ (¬ p4559))
    : (¬ p3212) ∨ (¬ p3556) ∨ (¬ p4107) ∨ (¬ p4135) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10139 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41331 (p2027 p2717 p3690 p3941 p4169 p4445 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h10140 : p2027 ∨ (¬ p2717) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p5122))
    : (¬ p2717) ∨ (¬ p3690) ∨ (¬ p3941) ∨ (¬ p4169) ∨ (¬ p4445) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10140 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41332 (p2027 p2509 p2881 p2922 p4277 p4383 : Prop)
    (h40810 : (¬ p2027))
    (h10141 : p2027 ∨ (¬ p2509) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p4277) ∨ (¬ p4383))
    : (¬ p2509) ∨ (¬ p2881) ∨ (¬ p2922) ∨ (¬ p4277) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10141 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41333 (p2027 p2437 p3574 p4137 p4620 p4710 : Prop)
    (h40810 : (¬ p2027))
    (h10142 : p2027 ∨ (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710))
    : (¬ p2437) ∨ (¬ p3574) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10142 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41334 (p2027 p2553 p3246 p4137 p4396 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h10143 : p2027 ∨ (¬ p2553) ∨ (¬ p3246) ∨ (¬ p4137) ∨ (¬ p4396) ∨ (¬ p4559))
    : (¬ p2553) ∨ (¬ p3246) ∨ (¬ p4137) ∨ (¬ p4396) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10143 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41335 (p2027 p3556 p3741 p3868 p4533 p5660 : Prop)
    (h40810 : (¬ p2027))
    (h10144 : p2027 ∨ (¬ p3556) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4533) ∨ (¬ p5660))
    : (¬ p3556) ∨ (¬ p3741) ∨ (¬ p3868) ∨ (¬ p4533) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3556 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10144 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41336 (p2027 p2563 p3389 p3646 p3904 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h10145 : p2027 ∨ (¬ p2563) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4646))
    : (¬ p2563) ∨ (¬ p3389) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10145 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41338 (p2027 p3073 p3692 p4119 p4140 p4317 p4435 p5472 : Prop)
    (h40810 : (¬ p2027))
    (h10147 : p2027 ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p4317) ∨ (¬ p4435) ∨ (¬ p5472))
    : (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p4317) ∨ (¬ p4435) ∨ (¬ p5472) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4317 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10147 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41339 (p2027 p2253 p2331 p2741 p3452 p4154 p4376 : Prop)
    (h40810 : (¬ p2027))
    (h10148 : p2027 ∨ (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2741) ∨ (¬ p3452) ∨ (¬ p4154) ∨ (¬ p4376))
    : (¬ p2253) ∨ (¬ p2331) ∨ (¬ p2741) ∨ (¬ p3452) ∨ (¬ p4154) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10148 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41341 (p2027 p2313 p2667 p3189 p4154 p4405 p4417 : Prop)
    (h40810 : (¬ p2027))
    (h10150 : p2027 ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417))
    : (¬ p2313) ∨ (¬ p2667) ∨ (¬ p3189) ∨ (¬ p4154) ∨ (¬ p4405) ∨ (¬ p4417) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10150 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41343 (p2027 p2553 p3016 p3359 p4022 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h10152 : p2027 ∨ (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4620))
    : (¬ p2553) ∨ (¬ p3016) ∨ (¬ p3359) ∨ (¬ p4022) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10152 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41345 (p2027 p2745 p2860 p2957 p3646 p3662 p4313 : Prop)
    (h40810 : (¬ p2027))
    (h10171 : p2027 ∨ (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4313))
    : (¬ p2745) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3662) ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2745 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10171 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41348 (p2027 p3051 p3646 p3744 p4140 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h10174 : p2027 ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4620))
    : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3744) ∨ (¬ p4140) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10174 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41349 (p2027 p2579 p3097 p3389 p4710 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10176 : p2027 ∨ (¬ p2579) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p4718))
    : (¬ p2579) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10176 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41350 (p2027 p2717 p3399 p3551 p3820 p3873 p4794 : Prop)
    (h40810 : (¬ p2027))
    (h10177 : p2027 ∨ (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4794))
    : (¬ p2717) ∨ (¬ p3399) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4794) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10177 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41351 (p2027 p2717 p2745 p3553 p3662 p4386 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h10178 : p2027 ∨ (¬ p2717) ∨ (¬ p2745) ∨ (¬ p3553) ∨ (¬ p3662) ∨ (¬ p4386) ∨ (¬ p4781))
    : (¬ p2717) ∨ (¬ p2745) ∨ (¬ p3553) ∨ (¬ p3662) ∨ (¬ p4386) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10178 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41352 (p2027 p2667 p2745 p2870 p2962 p3556 p4154 p4313 : Prop)
    (h40810 : (¬ p2027))
    (h10179 : p2027 ∨ (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p4154) ∨ (¬ p4313))
    : (¬ p2667) ∨ (¬ p2745) ∨ (¬ p2870) ∨ (¬ p2962) ∨ (¬ p3556) ∨ (¬ p4154) ∨ (¬ p4313) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2667 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h10179 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step41354 (p2027 p2088 p2534 p2881 p3960 p4186 p4277 : Prop)
    (h40810 : (¬ p2027))
    (h10183 : p2027 ∨ (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4186) ∨ (¬ p4277))
    : (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4186) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10183 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41355 (p2027 p2667 p2860 p2992 p3743 p4154 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h10184 : p2027 ∨ (¬ p2667) ∨ (¬ p2860) ∨ (¬ p2992) ∨ (¬ p3743) ∨ (¬ p4154) ∨ (¬ p5053))
    : (¬ p2667) ∨ (¬ p2860) ∨ (¬ p2992) ∨ (¬ p3743) ∨ (¬ p4154) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2667 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10184 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41356 (p2027 p2992 p4111 p4241 p4256 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h10203 : p2027 ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4256) ∨ (¬ p4608))
    : (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4256) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10203 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41357 (p2027 p2177 p2311 p2553 p2581 p3551 : Prop)
    (h40810 : (¬ p2027))
    (h10205 : p2027 ∨ (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p3551))
    : (¬ p2177) ∨ (¬ p2311) ∨ (¬ p2553) ∨ (¬ p2581) ∨ (¬ p3551) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2311 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10205 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41358 (p2027 p2284 p3051 p4110 p4320 p4539 : Prop)
    (h40810 : (¬ p2027))
    (h10206 : p2027 ∨ (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4539))
    : (¬ p2284) ∨ (¬ p3051) ∨ (¬ p4110) ∨ (¬ p4320) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10206 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41359 (p2027 p2748 p3136 p3359 p4111 p4241 p4949 : Prop)
    (h40810 : (¬ p2027))
    (h10207 : p2027 ∨ (¬ p2748) ∨ (¬ p3136) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4949))
    : (¬ p2748) ∨ (¬ p3136) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4241) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2748 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10207 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41360 (p2027 p2870 p3516 p3691 p3947 p4386 p5053 : Prop)
    (h40810 : (¬ p2027))
    (h10208 : p2027 ∨ (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p5053))
    : (¬ p2870) ∨ (¬ p3516) ∨ (¬ p3691) ∨ (¬ p3947) ∨ (¬ p4386) ∨ (¬ p5053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3691 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10208 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41361 (p2027 p2396 p2922 p3193 p4276 p4636 : Prop)
    (h40810 : (¬ p2027))
    (h10209 : p2027 ∨ (¬ p2396) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4276) ∨ (¬ p4636))
    : (¬ p2396) ∨ (¬ p2922) ∨ (¬ p3193) ∨ (¬ p4276) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10209 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41362 (p2027 p2589 p3016 p3389 p3742 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10210 : p2027 ∨ (¬ p2589) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4717))
    : (¬ p2589) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10210 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41364 (p2027 p2363 p2782 p2819 p3857 p4197 : Prop)
    (h40810 : (¬ p2027))
    (h10213 : p2027 ∨ (¬ p2363) ∨ (¬ p2782) ∨ (¬ p2819) ∨ (¬ p3857) ∨ (¬ p4197))
    : (¬ p2363) ∨ (¬ p2782) ∨ (¬ p2819) ∨ (¬ p3857) ∨ (¬ p4197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10213 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41366 (p2027 p3051 p3646 p3822 p4140 p4889 : Prop)
    (h40810 : (¬ p2027))
    (h10215 : p2027 ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3822) ∨ (¬ p4140) ∨ (¬ p4889))
    : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p3822) ∨ (¬ p4140) ∨ (¬ p4889) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4889 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10215 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41367 (p2027 p2476 p2662 p2810 p3136 p4241 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h10216 : p2027 ∨ (¬ p2476) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4608))
    : (¬ p2476) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10216 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41368 (p2027 p2098 p2363 p4232 p4859 p5339 : Prop)
    (h40810 : (¬ p2027))
    (h10217 : p2027 ∨ (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4232) ∨ (¬ p4859) ∨ (¬ p5339))
    : (¬ p2098) ∨ (¬ p2363) ∨ (¬ p4232) ∨ (¬ p4859) ∨ (¬ p5339) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4859 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5339 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10217 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41369 (p2027 p2140 p2870 p3246 p3821 p4984 : Prop)
    (h40810 : (¬ p2027))
    (h10218 : p2027 ∨ (¬ p2140) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984))
    : (¬ p2140) ∨ (¬ p2870) ∨ (¬ p3246) ∨ (¬ p3821) ∨ (¬ p4984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2140 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10218 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41370 (p2027 p2166 p3136 p3877 p4312 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h10219 : p2027 ∨ (¬ p2166) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4312) ∨ (¬ p4960))
    : (¬ p2166) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4312) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10219 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41372 (p2027 p2191 p2373 p2493 p4202 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10221 : p2027 ∨ (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2493) ∨ (¬ p4202) ∨ (¬ p4717))
    : (¬ p2191) ∨ (¬ p2373) ∨ (¬ p2493) ∨ (¬ p4202) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10221 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41373 (p2027 p2406 p2509 p2563 p3693 p4507 : Prop)
    (h40810 : (¬ p2027))
    (h10240 : p2027 ∨ (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507))
    : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p3693) ∨ (¬ p4507) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10240 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41374 (p2027 p2210 p2247 p2996 p4282 p4917 : Prop)
    (h40810 : (¬ p2027))
    (h10241 : p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p4282) ∨ (¬ p4917))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p4282) ∨ (¬ p4917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10241 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41375 (p2027 p2727 p3016 p3662 p3879 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10242 : p2027 ∨ (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4717))
    : (¬ p2727) ∨ (¬ p3016) ∨ (¬ p3662) ∨ (¬ p3879) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3879 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10242 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41376 (p2027 p2810 p2860 p2957 p3646 p4313 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10243 : p2027 ∨ (¬ p2810) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4704))
    : (¬ p2810) ∨ (¬ p2860) ∨ (¬ p2957) ∨ (¬ p3646) ∨ (¬ p4313) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10243 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41377 (p2027 p3083 p3136 p3364 p3874 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h10244 : p2027 ∨ (¬ p3083) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4704))
    : (¬ p3083) ∨ (¬ p3136) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10244 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41378 (p2027 p2589 p2659 p2992 p4111 p4241 : Prop)
    (h40810 : (¬ p2027))
    (h10245 : p2027 ∨ (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241))
    : (¬ p2589) ∨ (¬ p2659) ∨ (¬ p2992) ∨ (¬ p4111) ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10245 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41379 (p2027 p2331 p2542 p2589 p2655 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h10246 : p2027 ∨ (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4975))
    : (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10246 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41380 (p2027 p2331 p2440 p2657 p3984 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h10247 : p2027 ∨ (¬ p2331) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4717))
    : (¬ p2331) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3984) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10247 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41381 (p2027 p2331 p2737 p2811 p3585 p4343 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h10248 : p2027 ∨ (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975))
    : (¬ p2331) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10248 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41383 (p2027 p2166 p2950 p3136 p3412 p4120 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h10250 : p2027 ∨ (¬ p2166) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p4120) ∨ (¬ p4787))
    : (¬ p2166) ∨ (¬ p2950) ∨ (¬ p3136) ∨ (¬ p3412) ∨ (¬ p4120) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10250 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41384 (p2027 p2241 p2630 p2745 p3452 p4116 : Prop)
    (h40810 : (¬ p2027))
    (h10251 : p2027 ∨ (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3452) ∨ (¬ p4116))
    : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3452) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10251 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41385 (p2027 p3434 p3659 p3692 p4443 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h10252 : p2027 ∨ (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902))
    : (¬ p3434) ∨ (¬ p3659) ∨ (¬ p3692) ∨ (¬ p4443) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10252 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41386 (p2027 p2241 p2641 p3452 p4116 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h10254 : p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4975))
    : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10254 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41387 (p2027 p2478 p2509 p3222 p3857 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h10255 : p2027 ∨ (¬ p2478) ∨ (¬ p2509) ∨ (¬ p3222) ∨ (¬ p3857) ∨ (¬ p4695))
    : (¬ p2478) ∨ (¬ p2509) ∨ (¬ p3222) ∨ (¬ p3857) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2478 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10255 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41388 (p2027 p2534 p3073 p3238 p4610 p4688 : Prop)
    (h40810 : (¬ p2027))
    (h10256 : p2027 ∨ (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3238) ∨ (¬ p4610) ∨ (¬ p4688))
    : (¬ p2534) ∨ (¬ p3073) ∨ (¬ p3238) ∨ (¬ p4610) ∨ (¬ p4688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10256 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41389 (p2027 p2241 p2748 p3583 p3954 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h10257 : p2027 ∨ (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049))
    : (¬ p2241) ∨ (¬ p2748) ∨ (¬ p3583) ∨ (¬ p3954) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2748 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10257 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41390 (p2027 p3189 p3574 p4111 p4346 p4598 : Prop)
    (h40810 : (¬ p2027))
    (h10258 : p2027 ∨ (¬ p3189) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4598))
    : (¬ p3189) ∨ (¬ p3574) ∨ (¬ p4111) ∨ (¬ p4346) ∨ (¬ p4598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10258 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41391 (p2027 p2307 p2396 p2578 p4137 p4625 : Prop)
    (h40810 : (¬ p2027))
    (h10259 : p2027 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2578) ∨ (¬ p4137) ∨ (¬ p4625))
    : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2578) ∨ (¬ p4137) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10259 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41393 (p2027 p2383 p2578 p3016 p3742 p3921 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h10261 : p2027 ∨ (¬ p2383) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4405))
    : (¬ p2383) ∨ (¬ p2578) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10261 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41395 (p2027 p2563 p3125 p3946 p4198 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10263 : p2027 ∨ (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4533))
    : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10263 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41396 (p2027 p2187 p2387 p2563 p4198 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10264 : p2027 ∨ (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533))
    : (¬ p2187) ∨ (¬ p2387) ∨ (¬ p2563) ∨ (¬ p4198) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10264 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41397 (p2027 p2553 p3097 p3660 p3952 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h10265 : p2027 ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3952) ∨ (¬ p4702))
    : (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3952) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10265 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41398 (p2027 p2284 p2553 p4275 p4320 p4718 : Prop)
    (h40810 : (¬ p2027))
    (h10266 : p2027 ∨ (¬ p2284) ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4718))
    : (¬ p2284) ∨ (¬ p2553) ∨ (¬ p4275) ∨ (¬ p4320) ∨ (¬ p4718) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10266 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41399 (p2027 p2501 p2553 p3093 p4366 p4427 : Prop)
    (h40810 : (¬ p2027))
    (h10267 : p2027 ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427))
    : (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2501 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10267 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41400 (p2027 p2533 p3680 p4118 p4444 p5063 : Prop)
    (h40810 : (¬ p2027))
    (h10268 : p2027 ∨ (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p5063))
    : (¬ p2533) ∨ (¬ p3680) ∨ (¬ p4118) ∨ (¬ p4444) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2533 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10268 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41401 (p2027 p3146 p3266 p3657 p4191 p4623 p4905 : Prop)
    (h40810 : (¬ p2027))
    (h10269 : p2027 ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4191) ∨ (¬ p4623) ∨ (¬ p4905))
    : (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4191) ∨ (¬ p4623) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h10269 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step41402 (p2027 p2531 p3641 p3684 p4120 p4533 : Prop)
    (h40810 : (¬ p2027))
    (h10270 : p2027 ∨ (¬ p2531) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4120) ∨ (¬ p4533))
    : (¬ p2531) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p4120) ∨ (¬ p4533) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2531 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4533 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10270 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41403 (p2027 p2299 p2881 p3568 p3872 p4564 : Prop)
    (h40810 : (¬ p2027))
    (h10271 : p2027 ∨ (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4564))
    : (¬ p2299) ∨ (¬ p2881) ∨ (¬ p3568) ∨ (¬ p3872) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10271 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41404 (p2027 p3201 p3568 p3584 p4710 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10272 : p2027 ∨ (¬ p3201) ∨ (¬ p3568) ∨ (¬ p3584) ∨ (¬ p4710) ∨ (¬ p4973))
    : (¬ p3201) ∨ (¬ p3568) ∨ (¬ p3584) ∨ (¬ p4710) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10272 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41405 (p2027 p2177 p2553 p3553 p4067 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10273 : p2027 ∨ (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4973))
    : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10273 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41406 (p2027 p3324 p3584 p3641 p4157 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h10274 : p2027 ∨ (¬ p3324) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4157) ∨ (¬ p4973))
    : (¬ p3324) ∨ (¬ p3584) ∨ (¬ p3641) ∨ (¬ p4157) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3324 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4157 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10274 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step41407 (p2027 p2313 p2493 p2553 p2577 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h10275 : p2027 ∨ (¬ p2313) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p5191))
    : (¬ p2313) ∨ (¬ p2493) ∨ (¬ p2553) ∨ (¬ p2577) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h10275 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

end ElevenRUP
