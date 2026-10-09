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
    w, h = 520, 350
    poly: list[Point] = [(60, 80), (200, 40), (330, 90), (300, 170), (200, 140),
                         (240, 240), (90, 250)]
    a: Point = (130, 180)
    b: Point = (270, 205)
    body = stroke(path(poly), 3.5, INK, INSIDE)
    body += stroke(f"M {a[0]} {a[1]} L 500 {a[1]}", 2.2, ACCENT, dash="7 6")
    body += stroke(f"M {b[0]} {b[1]} L 20 {b[1]}", 2.2, "#5f3dc4", dash="7 6")
    body += dot((216, 180), 6, ACCENT)
    for x in (226, 82.1):
        body += dot((x, 205), 6, "#5f3dc4")
    body += dot(a, 6) + text(a[0] - 8, a[1] - 12, "A", 18, weight="bold")
    body += dot(b, 6) + text(b[0] + 14, b[1] - 10, "B", 18, weight="bold")
    body += text(40, 286, "A: 1 crossing (odd) ⇒ inside", 15, "start", ACCENT)
    body += text(280, 286, "B: 2 crossings (even) ⇒ outside", 15, "start", "#5f3dc4")
    body += text(260, 324, "For a polygon, the parity of ray crossings decides the side.", 15)
    return svg(w, h, body, "Ray-crossing parity decides inside or outside for a polygon")


def nonstandard_idea() -> str:
    w, h = 900, 380
    s = 88
    centers = [(150.0, 185.0), (450.0, 185.0), (750.0, 185.0)]
    body = ""
    titles = ["1. any continuous closed curve", "2. inscribe a polygon with",
              "3. take the standard shadow"]
    subtitles = ["(no smoothness assumed)", "infinitesimally short edges",
                 "deep inside / deep outside"]
    for (cx, _), t1, t2 in zip(centers, titles, subtitles):
        body += text(cx, 36, t1, 17, weight="bold") + text(cx, 58, t2, 14)

    cx, cy = centers[0]
    body += stroke(path(curve(cx, cy, s)), 3)

    cx, cy = centers[1]
    body += stroke(path(curve(cx, cy, s)), 6, HALO)
    poly = [blob(k / 28, cx, cy, s) for k in range(28)]
    body += stroke(path(poly), 2.2, INK, INSIDE)
    for p in poly:
        body += dot(p, 3, ACCENT)
    body += text(cx, 330, "vertices lie on the curve; the polygon is simple,", 13)
    body += text(cx, 348, "so the finite polygon Jordan theorem applies", 13)

    cx, cy = centers[2]
    body += f'<rect x="{cx - 140}" y="78" width="280" height="225" rx="14" fill="{OUTSIDE}"/>\n'
    body += stroke(path(curve(cx, cy, s)), 14, HALO, INSIDE)
    body += stroke(path(curve(cx, cy, s)), 2.5)
    body += text(cx, cy + 5, "standard inside", 15, weight="bold")
    body += text(cx + 112, 98, "standard", 13) + text(cx + 112, 114, "outside", 13)
    body += text(cx, 330, "grey halo = points infinitely close to the curve;", 13)
    body += text(cx, 348, "its shadow is exactly the original curve", 13)

    for x0 in (262, 562):
        body += stroke(f"M {x0} 185 L {x0 + 36} 185 M {x0 + 26} 175 L {x0 + 36} 185 "
                       f"L {x0 + 26} 195", 3, ACCENT)
    return svg(w, h, body, "Approximate by an infinitesimal polygon, then take standard parts")


def main() -> None:
    figures = {
        "inside-outside.svg": inside_outside(),
        "ray-parity.svg": ray_parity(),
        "nonstandard-idea.svg": nonstandard_idea(),
    }
    for name, content in figures.items():
        (HERE / name).write_text(content, encoding="utf-8")
        print(f"wrote docs/figures/{name}")


if __name__ == "__main__":
    main()
