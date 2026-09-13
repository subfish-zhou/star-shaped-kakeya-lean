#!/usr/bin/env python3
"""Exact certificate that the 32-segment schedule witnesses C_FS >= 141/2000."""
from fractions import Fraction as Q
import json
from pathlib import Path

def require(name, condition):
    if not condition: raise AssertionError(name)

def qstr(x): return f"{x.numerator}/{x.denominator}"

def log_upper_ratio(y, terms=3):
    require("log argument", y >= 1)
    z=(y-1)/(y+1); require("atanh range", 0 <= z < 1)
    partial=sum((z**(2*j+1)/Q(2*j+1) for j in range(terms)),Q(0))
    tail=z**(2*terms+1)/(Q(2*terms+1)*(1-z*z))
    return 2*(partial+tail)

def ledger_lower(a,b,R):
    require("ledger interval", 0 <= a <= b <= R)
    return -(b*b-a*a)/2+2*R*(b-a)-2*R*R*log_upper_ratio((R+b)/(R+a))

def main():
    eta=Q(141046,1000000)
    target=Q(141,2000)
    common=Q(22447,1000000)
    pi_lower=Q(333,106)
    b=[
        Q(27226, 1000000), Q(38590, 1000000), Q(47324, 1000000), Q(54682, 1000000), Q(61151, 1000000), Q(66981, 1000000), Q(72321, 1000000), Q(77266, 1000000), Q(81884, 1000000), Q(86225, 1000000), Q(90323, 1000000), Q(94208, 1000000), Q(97900, 1000000), Q(101419, 1000000), Q(104778, 1000000), Q(107987, 1000000), Q(111058, 1000000), Q(113996, 1000000), Q(116807, 1000000), Q(119496, 1000000), Q(122066, 1000000), Q(124519, 1000000), Q(126854, 1000000), Q(129071, 1000000), Q(131166, 1000000), Q(133135, 1000000), Q(134969, 1000000), Q(136656, 1000000), Q(138174, 1000000), Q(139487, 1000000), Q(140523, 1000000), Q(141046, 1000000)
    ]
    R=[
        Q(500000, 1000000), Q(500740, 1000000), Q(501486, 1000000), Q(502234, 1000000), Q(502981, 1000000), Q(503725, 1000000), Q(504466, 1000000), Q(505203, 1000000), Q(505934, 1000000), Q(506660, 1000000), Q(507380, 1000000), Q(508092, 1000000), Q(508797, 1000000), Q(509494, 1000000), Q(510182, 1000000), Q(510860, 1000000), Q(511528, 1000000), Q(512185, 1000000), Q(512830, 1000000), Q(513462, 1000000), Q(514081, 1000000), Q(514684, 1000000), Q(515271, 1000000), Q(515841, 1000000), Q(516390, 1000000), Q(516918, 1000000), Q(517421, 1000000), Q(517896, 1000000), Q(518338, 1000000), Q(518740, 1000000), Q(519092, 1000000), Q(519371, 1000000)
    ]
    t=[
        Q(27226, 1000000), Q(339842, 1000000), Q(344933, 1000000), Q(349939, 1000000), Q(354888, 1000000), Q(359794, 1000000), Q(364671, 1000000), Q(369526, 1000000), Q(374368, 1000000), Q(379204, 1000000), Q(384040, 1000000), Q(388883, 1000000), Q(393740, 1000000), Q(398615, 1000000), Q(403517, 1000000), Q(408452, 1000000), Q(413428, 1000000), Q(418453, 1000000), Q(423537, 1000000), Q(428690, 1000000), Q(433923, 1000000), Q(439251, 1000000), Q(444691, 1000000), Q(450264, 1000000), Q(455995, 1000000), Q(461917, 1000000), Q(468075, 1000000), Q(474531, 1000000), Q(481375, 1000000), Q(488752, 1000000), Q(496925, 1000000), Q(506472, 1000000), Q(519371, 1000000)
    ]
    n=len(b); require("32 classes",n==32 and len(R)==n and len(t)==n+1)
    require("eta endpoint",b[-1]==eta)
    require("class order",all(b[i]<b[i+1] for i in range(n-1)))
    require("radius order",all(R[i]<R[i+1] for i in range(n-1)))
    require("switch order",all(t[i]<t[i+1] for i in range(n)))
    require("schedule begins at first cap",t[0]==b[0])
    require("radial budget",all(t[i+1]<=R[i] for i in range(n)))
    rows=[]; margins=[]; prev=Q(0)
    for j in range(n):
        geom=Q(1,4)+prev*prev-R[j]*R[j]
        require(f"geometry {j}",geom>=0)
        payment=ledger_lower(b[j],t[1],R[0])
        for k in range(1,j+1): payment+=ledger_lower(t[k],t[k+1],R[k])
        margin=payment-common; require(f"payment {j}",margin>0); margins.append(margin)
        rows.append({"j":j,"m_lower":qstr(prev),"m_upper":qstr(b[j]),"R":qstr(R[j]),"geometry_margin":qstr(geom),"payment_lower":qstr(payment),"margin":qstr(margin),"payment_decimal":float(payment)})
        prev=b[j]
    # High half-unit bands.
    r0_lower=Q(5049,5000); b0=eta+Q(1,2)
    require("R0 lower square",1+eta*eta>r0_lower*r0_lower)
    width=r0_lower-b0; require("width positive",width>0)
    factor=(eta+Q(1,2))/(2*eta+Q(3,2))
    high=factor*width*width/2; require("high payment",high>common)
    require("low high separation",t[-1]<b0)
    pi_margin=common*pi_lower-target; require("pi comparison",pi_margin>0)
    height_margin=eta/2-target; require("height comparison",height_margin>0)
    gain=target-Q(7,100); require("gain",gain==Q(1,2000))
    result={"parameters":{"eta":qstr(eta),"target":qstr(target),"common":qstr(common),"pi_lower":qstr(pi_lower),"log_terms":3},"schedule":{"b":[qstr(x) for x in b],"R":[qstr(x) for x in R],"t":[qstr(x) for x in t],"rows":rows,"minimum_payment_margin":qstr(min(margins)),"minimum_payment_margin_decimal":min(x["payment_decimal"]-float(common) for x in rows)},"high":{"R0_lower":qstr(r0_lower),"width_lower":qstr(width),"factor_lower":qstr(factor),"coefficient_lower":qstr(high),"margin":qstr(high-common)},"final":{"pi_margin":qstr(pi_margin),"height_margin":qstr(height_margin),"gain_over_7_100":qstr(gain)},"status":"ONE_FORTY_ONE_OVER_TWO_THOUSAND_CERTIFICATE_OK"}
    out=Path(__file__).with_name("one_forty_one_over_two_thousand_certificate.json")
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2));print(result["status"])
if __name__=="__main__":main()
