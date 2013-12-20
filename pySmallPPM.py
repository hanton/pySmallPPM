"""Introduction

pySmallPPM, A Python Progressive Photon Mapping Tracer, by Hanton Yang, 2013
originally smallppm, A Progressive Photon Mapping Tracer, by T. Hachisuka
Usage: pypy pySmallPPM.py or python pySmallPPM.py

"""
import time
import sys
from math import pi, cos, sin, acos, sqrt, exp
from collections import namedtuple

ALPHA = 0.7

primes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,
          89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,
          179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,
          269,271,277,281,283]

def rev(i, p):
    if i == 0:
        return i
    else:
        return p - i


# Halton Sequence with Reverse Permutation
def hal(b, j):
    p = primes[b]
    f = 1.0 / p
    fct = f
    h = 0.0
    while j > 0:
        h += rev(j % p, p) * fct
        j /= p
        fct *= f
    return h


class Vector(object):
    def __init__(self, x, y, z):
        self.x, self.y, self.z = float(x), float(y), float(z)

    def __str__(self):
        return "(%s,%s,%s)" % (self.x, self.y, self.z)

    def __repr__(self):
        return "Vector" + str(self)

    def __add__(self, other):
        return Vector(self.x+other.x, self.y+other.y, self.z+other.z)

    def __sub__(self, other):
        return Vector(self.x-other.x, self.y-other.y, self.z-other.z)

    def __mul__(self, other):
        if type(other) == Vector:
            # Dot Multiple
            return self.x*other.x + self.y*other.y + self.z*other.z
        else:
            # Scale
            return Vector(self.x*other, self.y*other, self.z*other)

    def __rmul__(self, other):
        if type(other) == Vector:
            # dot multiple
            return self.x*other.x + self.y*other.y + self.z*other.z
        else:
            # scale
            return Vector(self.x*other, self.y*other, self.z*other)

    def __div__(self, other):
        return Vector(self.x/other, self.y/other, self.z/other)

    def __xor__(self, other):
        return Vector(self.y*other.z - self.z*other.y,
                      self.z*other.x - self.x*other.z,
                      self.x*other.y - self.y*other.x)

    def length(self):
        return sqrt(self.x*self.x + self.y*self.y + self.z*self.z)

    def normalize(self):
        return self / sqrt(self.x*self.x + self.y*self.y + self.z*self.z)


class Color(object):
    def __init__(self, red, green, blue):
        self.r, self.g, self.b = red, green, blue

    def __str__(self):
        return "(%s,%s,%s)" % (self.r, self.g, self.b)

    def __repr__(self):
        return "Color" + str(self)

    def __add__(self, other):
        return Color(self.r+other.r, self.g+other.g, self.b+other.b)

    def __sub__(self, other):
        return Color(self.r-other.r, self.g-other.g, self.b-other.b)

    def __mul__(self, other):
        if type(other) == Color:
            return Color(self.r*other.r, self.g*other.g, self.b*other.b)
        else:
            return Color(self.r*other, self.g*other, self.b*other)

    def __rmul__(self, other):
        if type(other) == Color:
            return Color(self.r*other.r, self.g*other.g, self.b*other.b)
        else:
            return Color(self.r*other, self.g*other, self.b*other)

    def __div__(self, other):
        return Color(self.r/other, self.g/other, self.b/other)


class BBox(object):
    def __init__(self):
        self.min_ = Vector(0.0, 0.0, 0.0)
        self.max_ = Vector(0.0, 0.0, 0.0)

    def fit(self, p):
        self.min_.x = min(p.x, self.min_.x)
        self.min_.y = min(p.y, self.min_.y)
        self.min_.z = min(p.z, self.min_.z)
        self.max_.x = max(p.x, self.max_.x)
        self.max_.y = max(p.y, self.max_.y)
        self.max_.z = max(p.z, self.max_.z)

    def reset(self):
        self.min_ = Vector(1e20, 1e20, 1e20)
        self.max_ = Vector(-1e20, -1e20, -1e20)


# unsigned n
class HPoint(object):
    def __init__(self):
        self.f = Color(0.0, 0.0, 0.0)
        self.pos = Vector(0.0, 0.0, 0.0)
        self.nrm = Vector(0.0, 0.0, 0.0)
        self.flux = Color(0.0, 0.0, 0.0)
        self.r2 = 0.0
        self.n = 0
        self.pix = 0


#unsigned
num_hash = 0
pixel_index = 0
num_photon = 0

hash_s = 0.0
hash_grid = []
hitpoints = []
hpbbox = BBox()


def unsigned(i):
    return i & 0xffffffff


#unsigned
def hash_function(ix, iy, iz):
    #return unsigned((ix*73856093)^(iy*19349663)^(iz*83492791) % num_hash)
    return (((ix*73856093)^(iy*19349663)^(iz*83492791)) % num_hash)


def build_hash_grid(w, h):
    global hpbbox, hitpoints, hash_s, num_hash, hash_grid
    hpbbox.reset()
    for hp in hitpoints:
        hpbbox.fit(hp.pos)
    ssize = hpbbox.max_ - hpbbox.min_  # Computer Initial Radius
    irad = ((ssize.x+ssize.y+ssize.z)/3.0) / ((w+h)/2.0) * 2.0
    vec_irad = Vector(irad, irad, irad)
    hpbbox.reset()
    vphoton = 0  # Determine Hash Size
    for i in xrange(len(hitpoints)):
        hitpoints[i].r2 = irad * irad
        hitpoints[i].n = 0
        hitpoints[i].flux = Color(0.0, 0.0, 0.0)
        vphoton += 1
        hpbbox.fit(hitpoints[i].pos - vec_irad)
        hpbbox.fit(hitpoints[i].pos + vec_irad)
    hash_s = 1.0 / (irad*2.0)
    num_hash = vphoton
    for i in xrange(num_hash):
        hash_grid.append([])
    for hp in hitpoints:
        BMin = ((hp.pos-vec_irad)-hpbbox.min_) * hash_s
        BMax = ((hp.pos+vec_irad)-hpbbox.min_) * hash_s
        for iz in xrange(abs(int(BMin.z)), abs(int(BMax.z))+1):
            for iy in xrange(abs(int(BMin.y)), abs(int(BMax.y))+1):
                for ix in xrange(abs(int(BMin.x)), abs(int(BMax.x))+1):
                    hv = hash_function(ix, iy, iz)
                    #hash_grid[hv].insert(0, hp)
                    hash_grid[hv].append(hp)


class Ray(object):
    def __init__(self, origin, direction):
        self.origin = origin
        self.direction = direction


class Sphere(object):
    def __init__(self, radius, position, color, material):
        self.radius = radius
        self.position = position
        self.color = color
        self.material = material

    def intersect(self, ray):
        op = self.position - ray.origin
        eps = 1e-4
        b = op * ray.direction
        det = b*b - op*op + self.radius*self.radius

        if det < 0.0:
            return 0.0
        else:
            det = sqrt(det)

        t = b - det
        if t > eps:
            return t

        t = b + det
        if t > eps:
            return t

        return 0.0


spheres = []
# Left
radius = 1e5
position = Vector(1e5+1, 40.8, 81.6)
color = Color(.75, .25, .25)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Rght
radius = 1e5
position = Vector(-1e5+99, 40.8, 81.6)
color = Color(.25, .25, .75)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Back
radius = 1e5
position = Vector(50, 40.8, 1e5)
color = Color(.75, .75, .75)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Front
radius = 1e5
position = Vector(50, 40.8, -1e5+170)
color = Color(0.0, 0.0, 0.0)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Bottom
radius = 1e5
position = Vector(50, 1e5, 81.6)
emission = Color(0.0, 0.0, 0.0)
color = Color(.75, .75, .75)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Top
radius = 1e5
position = Vector(50, -1e5+81.6, 81.6)
color = Color(.75, .75, .75)
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Mirror
radius = 16.5
position = Vector(27, 16.5, 47)
color = Color(1, 1, 1)*.999
material = "specular"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Glass
radius = 16.5
position = Vector(73, 16.5, 88)
color = Color(1, 1, 1) * .999
material = "refractive"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)
# Middle Diffuse Sphere
radius = 8.5
position = Vector(50, 8.5, 60)
color = Color(1, 1, 1) * .999
material = "diffuse"
sphere = Sphere(radius, position, color, material)
spheres.append(sphere)


def toInt(x):
    return chr(int(pow(1-exp(-x), 1.0 / 2.2)*255.0 + 0.5))


def intersect(ray):
    inf = t = 1e20
    d = 0.0
    hit_object = None
    for sphere in spheres:
        d = sphere.intersect(ray)
        if d != 0.0 and d < t:
            t = d
            hit_object = sphere
    hit = (t < inf)
    return hit, t, hit_object


def genp(i):
    f = Vector(2500, 2500, 2500) * (pi*4.0)
    p = 2.0 * pi * hal(0, i)
    t = 2.0 * acos(sqrt(1.0-hal(1, i)))
    st = sin(t)
    ray_direction = Vector(cos(p)*st, cos(t), sin(p)*st)
    ray_origin = Vector(50, 60, 85)
    ray = Ray(ray_origin, ray_direction)
    return ray, f


def trace(ray, depth, m, fl, adj, i):
    global hitpoints, hash_grid

    depth += 1
    hit, t, hit_object = intersect(ray)
    if (hit is False) or (depth>=20):
        return
    d3 = depth * 3
    x = ray.origin + t*ray.direction
    n = (x - hit_object.position).normalize()
    f = hit_object.color
    if n*ray.direction < 0.0:
        nl = n
    else:
        nl = -1.0 * n
    p = max(f.r, f.g, f.b)

    if hit_object.material == 'diffuse':
        r1 = 2.0 * pi * hal(d3-1, i)
        r2 = hal(d3+0, i)
        r2s = sqrt(r2)
        w = nl
        if abs(w.x) > 0.1:
            u = Vector(0.0, 1.0, 0.0) ^ w
        else:
            u = Vector(1.0, 1.0, 1.0) ^ w
        u = u.normalize()
        v = w ^ u
        d = u*cos(r1)*r2s + v*sin(r1)*r2s + w*sqrt(1.0 - r2)
        d = d.normalize()
        if m:
            hp = HPoint()
            hp.f = f * adj
            hp.pos = x
            hp.nrm = n
            hp.pix = pixel_index
            #hitpoints.insert(0, hp)
            hitpoints.append(hp)
        else:
            hh = (x-hpbbox.min_) * hash_s
            ix = abs(int(hh.x))
            iy = abs(int(hh.y))
            iz = abs(int(hh.z))
            hash_number = hash_function(ix, iy, iz)
            hlist = hash_grid[hash_number]
            for index in xrange(len(hlist)):
                v = hlist[index].pos - x
                if (hlist[index].nrm*n > 1e-3) and (v*v <= hlist[index].r2):
                    g = (hlist[index].n*ALPHA+ALPHA) / (hlist[index].n*ALPHA+1.0)
                    hlist[index].r2 = hlist[index].r2 * g
                    hlist[index].n += 1
                    hlist[index].flux += hlist[index].f * fl * (1.0/pi)
                    hlist[index].flux *= g
            hash_grid[hash_number] = hlist
            if hal(d3+1, i) < p:
                trace(Ray(x, d), depth, m, f*fl*(1.0/p), adj, i)
    elif hit_object.material == 'specular':
        reflect_ray_direction = ray.direction - n*2.0*(n*ray.direction)
        reflect_ray = Ray(x, reflect_ray_direction)
        trace(reflect_ray, depth, m, f*fl, f*adj, i)
    else:
        # Ideal Dielectric Refraction
        reflect_ray_direction = ray.direction - n*2.0*n*ray.direction
        reflect_ray = Ray(x, reflect_ray_direction)
        into = (n*nl > 0.0)
        nc = 1.0
        nt = 1.5
        if into:
            nnt = nc / nt
        else:
            nnt = nt / nc
        ddn = ray.direction * nl
        cos2t = 1.0 - nnt*nnt*(1.0-ddn*ddn)
        if cos2t < 0.0:
            return trace(reflect_ray, depth, m, fl, adj, i)
        if into:
            tdir = ray.direction*nnt - n*(ddn*nnt + sqrt(cos2t))
        else:
            tdir = ray.direction*nnt - (-1.0)*n*(ddn*nnt + sqrt(cos2t))
        tdir = tdir.normalize()
        a = nt - nc
        b = nt + nc
        R0 = (a*a) / (b*b)
        if into:
            c = 1.0 - (-ddn)
        else:
            c = 1.0 - (tdir*n)
        Re = R0 + (1.0-R0) * pow(c, 5)
        P = Re
        refract_ray = Ray(x, tdir)
        fa = f * adj
        if m:
            trace(reflect_ray, depth, m, fl, fa*Re, i)
            trace(refract_ray, depth, m, fl, fa*(1.0-Re), i)
        else:
            if hal(d3-1, i) < P:
                trace(reflect_ray, depth, m, fl, fa, i)
            else:
                trace(refract_ray, depth, m, fl, fa, i)
        

def smallppm():
    global pixel_index, num_photon

    start_time = time.time()

    width, height = 1024, 768
    samples = 1
    if len(sys.argv) == 2:
        samples = int(sys.argv[1]) / 1000

    camera_origin = Vector(50, 48, 295.6)
    camera_direction = Vector(0, -0.042612, -1).normalize()
    cx = width * 0.5135 / height
    cx = Vector(cx, 0.0, 0.0)
    cy = (cx ^ camera_direction).normalize() * 0.5135
    
    pixels = []
    for i in xrange(height * width):
        pixels.append(Color(0.0, 0.0, 0.0))

    for y in xrange(height):
        text = "\rHitPointPass: {0:.2f}%".format(100.0 * y / (height-1))
        sys.stdout.write(text)
        sys.stdout.flush()
        for x in xrange(width):
            pixel_index = y*width + x
            c_x = cx * ((x+0.5)/width - 0.5)
            c_y = cy * (-(y+0.5)/height + 0.5)
            d = c_x + c_y + camera_direction
            ray_origin = camera_origin + d*135.0
            ray_direction = d.normalize()
            ray = Ray(ray_origin, ray_direction)
            trace(ray, 0, True, Vector(0.0, 0.0, 0.0), Vector(1, 1, 1), 0) 
    build_hash_grid(width, height)
    num_photon = samples
    vw = Vector(1.0, 1.0, 1.0)

    for i in xrange(num_photon):
        text = "\rPhotonPass: {0:.2f}%".format(100.0 * (i+1) / num_photon)
        sys.stdout.write(text)
        sys.stdout.flush()
        m = 1000 * i
        for j in xrange(1000):
            ray, f = genp(m + j)
            trace(ray, 0, 0>1, f, vw, m+j)
    for hp in hitpoints:
        i = hp.pix
        pixels[i] += hp.flux * (1.0/(pi*hp.r2*num_photon*1000.0))

    with open('pySmallPPM.ppm', 'wb') as f:
        f.write('P6 %d %d 255\n' % (width, height))
        for pixel in pixels:
            f.write(toInt(pixel.r) + toInt(pixel.g) + toInt(pixel.b))
        f.close()

    end_time = time.time()
    print "\rRender Time: %i seconds." % (end_time - start_time)


if __name__ == '__main__':
    smallppm()
