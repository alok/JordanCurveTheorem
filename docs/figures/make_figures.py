#!/usr/bin/env python3
"""Regenerate the explainer figures: `python3 docs/figures/make_figures.py`.

Every figure has an explicit white background so it reads on light and dark GitHub themes.
"""

from __future__ import annotations

import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
FONT = "font-family=\"'Comic Sans MS', 'Chalkboard SE', 'Segoe Print', cursive, sans-serif\""
INK = "#1f2933"
INSIDE = "#bfe0ff"
OUTSIDE = "#fff1c9"
HALO = "#c8c8c8"
ACCENT = "#d9480f"
VIOLET = "#5f3dc4"

Point = tuple[float, float]


def blob(t: float, cx: float, cy: float, scale: float) -> Point:
    """A wobbly but simple closed curve, parametrized by t ∈ [0, 1)."""
    a = 2 * math.pi * t
    r = 1 + 0.22 * math.sin(3 * a) + 0.08 * math.cos(5 * a + 0.7)
    return (cx + scale * r * math.cos(a), cy + scale * 0.85 * r * math.sin(a))


def path(points: list[Point], closed: bool = True) -> str:
    d = "M " + " L ".join(f"{x:.1f} {y:.1f}" for x, y in points)
    return d + (" Z" if closed else "")


def curve(cx: float, cy: float, scale: float, n: int = 240) -> list[Point]:
    return [blob(k / n, cx, cy, scale) for k in range(n)]


def svg(width: int, height: int, body: str, title: str) -> str:
    return (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" role="img" aria-label="{title}">\n'
        f"<title>{title}</title>\n"
        f'<rect x="0" y="0" width="{width}" height="{height}" fill="#ffffff"/>\n'
        f"{body}</svg>\n"
    )


def text(x: float, y: float, s: str, size: int = 15, anchor: str = "middle",
         color: str = INK, weight: str = "normal") -> str:
    return (f'<text x="{x:.1f}" y="{y:.1f}" {FONT} font-size="{size}" '
            f'text-anchor="{anchor}" fill="{color}" font-weight="{weight}">{s}</text>\n')


def dot(p: Point, r: float = 4, color: str = INK) -> str:
    return f'<circle cx="{p[0]:.1f}" cy="{p[1]:.1f}" r="{r}" fill="{color}"/>\n'


def stroke(d: str, width: float = 3, color: str = INK, fill: str = "none",
           dash: str | None = None) -> str:
    extra = f' stroke-dasharray="{dash}"' if dash else ""
    return (f'<path d="{d}" fill="{fill}" stroke="{color}" stroke-width="{width}" '
            f'stroke-linejoin="round" stroke-linecap="round"{extra}/>\n')


def inside_outside() -> str:
    w, h = 520, 330
    pts = curve(250, 170, 115)
    body = f'<rect x="10" y="10" width="{w - 20}" height="{h - 20}" rx="18" fill="{OUTSIDE}"/>\n'
    body += stroke(path(pts), 3.5, INK, INSIDE)
    body += text(250, 178, "inside", 24, weight="bold")
    body += text(250, 202, "bounded", 14)
    body += text(445, 50, "outside", 24, weight="bold")
    body += text(445, 72, "unbounded", 14)
    body += text(98, 300, "the curve itself: the common boundary", 14, "start")
    foot = pts[80]
    body += stroke(f"M 110 286 Q 100 {foot[1] + 20:.1f} {foot[0]:.1f} {foot[1]:.1f}", 1.8, ACCENT)
    body += dot(foot, 5, ACCENT)
    return svg(w, h, body, "A simple closed curve splits the plane into an inside and an outside")


def ray_parity() -> str:
    w, h = 520, 370
    poly: list[Point] = [(60, 80), (200, 40), (330, 90), (300, 170), (200, 140),
                         (240, 240), (90, 250)]
    a: Point = (130, 180)
    b: Point = (270, 205)
    body = stroke(path(poly), 3.5, INK, INSIDE)
    body += stroke(f"M {a[0]} {a[1]} L 500 {a[1]}", 2.2, ACCENT, dash="7 6")
    body += stroke(f"M {b[0]} {b[1]} L 20 {b[1]}", 2.2, VIOLET, dash="7 6")
    body += dot((216, 180), 6, ACCENT)
    for x in (226, 82.1):
        body += dot((x, 205), 6, VIOLET)
    body += dot(a, 6) + text(a[0] - 8, a[1] - 12, "A", 18, weight="bold")
    body += dot(b, 6) + text(b[0] + 14, b[1] - 10, "B", 18, weight="bold")
    body += text(30, 286, "A: 1 crossing (odd), so A is inside", 16, "start", ACCENT, "bold")
    body += text(30, 310, "B: 2 crossings (even), so B is outside", 16, "start", VIOLET, "bold")
    body += text(30, 346, "For a polygon, counting crossings decides the side.", 15, "start")
    return svg(w, h, body, "Ray-crossing parity decides inside or outside for a polygon")


def nonstandard_idea() -> str:
    w, h = 960, 390
    s = 88
    centers = [(160.0, 190.0), (480.0, 190.0), (800.0, 190.0)]
    body = ""
    titles = ["1. any continuous closed curve", "2. inscribe a polygon with",
              "3. bring it back to the plane"]
    subtitles = ["(no smoothness assumed)", "infinitesimally short edges",
                 "deep inside / deep outside"]
    for (cx, _), t1, t2 in zip(centers, titles, subtitles):
        body += text(cx, 36, t1, 18, weight="bold") + text(cx, 60, t2, 16)

    cx, cy = centers[0]
    body += stroke(path(curve(cx, cy, s)), 3)

    cx, cy = centers[1]
    body += stroke(path(curve(cx, cy, s)), 6, HALO)
    poly = [blob(k / 28, cx, cy, s) for k in range(28)]
    body += stroke(path(poly), 2.2, INK, INSIDE)
    for p in poly:
        body += dot(p, 3, ACCENT)
    body += text(cx, 336, "vertices on the curve; edges do not cross,", 15)
    body += text(cx, 357, "so the finite polygon theorem applies", 15)
    body += text(cx, 378, "(grey: the curve, behind the polygon)", 15)

    cx, cy = centers[2]
    body += f'<rect x="{cx - 145}" y="82" width="290" height="225" rx="14" fill="{OUTSIDE}"/>\n'
    body += stroke(path(curve(cx, cy, s)), 3, INK, INSIDE)
    body += text(cx, cy + 5, "standard inside", 16, weight="bold")
    body += text(cx + 108, 104, "standard", 15) + text(cx + 108, 122, "outside", 15)
    body += text(cx, 336, "the polygon's shadow is exactly", 15)
    body += text(cx, 357, "the original curve, which separates", 15)
    body += text(cx, 378, "the two standard regions", 15)

    for x0 in (277, 597):
        body += stroke(f"M {x0} 190 L {x0 + 36} 190 M {x0 + 26} 180 L {x0 + 36} 190 "
                       f"L {x0 + 26} 200", 3, ACCENT)
    return svg(w, h, body, "Approximate by an infinitesimal polygon, then take standard parts")


def lens(center: Point, r: float, body: str, clip_id: str) -> str:
    """A magnifying circle: `body` is drawn clipped to the disc of radius `r`."""
    cx, cy = center
    return (f'<clipPath id="{clip_id}"><circle cx="{cx}" cy="{cy}" r="{r}"/></clipPath>\n'
            f'<g clip-path="url(#{clip_id})">\n{body}</g>\n'
            f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="none" stroke="{INK}" '
            f'stroke-width="2.5"/>\n')


def deep_vs_curve() -> str:
    w, h = 740, 430
    body = text(w / 2, 34, "Zooming in on a point's monad", 20, weight="bold")
    body += f'<rect x="20" y="62" width="300" height="300" rx="16" fill="{OUTSIDE}"/>\n'
    pts = curve(165, 212, 112)
    body += stroke(path(pts), 3, INK, INSIDE)
    a: Point = (120, 190)
    b = pts[0]
    body += dot(a, 6) + text(a[0] - 4, a[1] - 20, "a", 20, weight="bold")
    body += dot(b, 6) + text(b[0] + 4, b[1] - 20, "b", 20, weight="bold")

    ca: Point = (510, 140)
    cb: Point = (510, 312)
    r = 72
    for (px, py), (qx, qy) in ((a, ca), (b, cb)):
        body += f'<circle cx="{px}" cy="{py}" r="12" fill="none" stroke="{INK}" stroke-width="1.8"/>\n'
        body += stroke(f"M {px + 12:.1f} {py:.1f} L {qx - r:.1f} {qy:.1f}", 1.6, INK, dash="5 5")

    inner_a = f'<rect x="{ca[0] - r}" y="{ca[1] - r}" width="{2 * r}" height="{2 * r}" fill="{INSIDE}"/>\n'
    body += lens(ca, r, inner_a + dot(ca, 6), "lens-a")

    # Inside the monad of b, the infinitesimal polygon passes infinitely close to b.
    zig = [(cb[0] - 22 + (14 if k % 2 else 0) + 3 * k, cb[1] - r - 10 + k * 19)
           for k in range(10)]
    region = path([(cb[0] - r - 10, cb[1] - r - 10), *zig, (cb[0] - r - 10, cb[1] + r + 10)])
    inner_b = f'<rect x="{cb[0] - r}" y="{cb[1] - r}" width="{2 * r}" height="{2 * r}" fill="{OUTSIDE}"/>\n'
    inner_b += stroke(region, 0, INSIDE, INSIDE)
    inner_b += stroke(path(zig, closed=False), 2.5, INK)
    for p in zig:
        inner_b += dot(p, 3, ACCENT)
    body += lens(cb, r, inner_b + dot((cb[0] + 6, cb[1]), 6), "lens-b")

    body += text(596, 120, "monad of a:", 15, "start", weight="bold")
    body += text(596, 140, "all inside", 15, "start")
    body += text(596, 160, "the polygon", 15, "start")
    body += text(596, 292, "monad of b:", 15, "start", weight="bold")
    body += text(596, 312, "the polygon", 15, "start")
    body += text(596, 332, "cuts through it", 15, "start")
    body += text(30, 392, "a is deep inside, so a is in the standard inside.", 15, "start")
    body += text(30, 414, "b is on the curve: its monad meets both sides, so b is in neither region.",
                 15, "start")
    return svg(w, h, body, "A deep inside point has its whole monad inside the polygon; "
               "a point on the curve does not")


def main() -> None:
    figures = {
        "inside-outside.svg": inside_outside(),
        "ray-parity.svg": ray_parity(),
        "nonstandard-idea.svg": nonstandard_idea(),
        "deep-vs-curve.svg": deep_vs_curve(),
    }
    for name, content in figures.items():
        (HERE / name).write_text(content, encoding="utf-8")
        print(f"wrote docs/figures/{name}")


if __name__ == "__main__":
    main()
