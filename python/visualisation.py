import numpy as np
import common
import piio

def plot_line(im, x1, y1, x2, y2, colour):
    """
    Plots a line on a rgb image stored as a numpy array

    Args:
        im: 3D numpy array containing the image values. It may be stored as
            uint8 or float32.
        x1, y1, x2, y2: coordinates of the line endpoints
        colour: list of length 3 giving the colour used for the plotted line
            (ie [r, g, b])

    Returns:
        a copy of the input numpy array, with the plotted lines on it. It means
        that the intensities of pixels located on the plotted line are changed.
    """
    # convert endpoints to int
    x1, y1, x2, y2 = np.round(x1), np.round(y1), np.round(x2), np.round(y2)

    # colour points of the line pixel by pixel. Loop over x or y, depending on
    # the biggest dimension.
    if np.abs(x2 - x1) >= np.abs(y2 - y1):
        n = np.abs(x2 - x1)
        for i in range(int(n+1)):
            x = x1 + i * (x2 - x1) / n
            y = np.round(y1 + i * (y2 - y1) / n)
            im[y, x] = colour
    else:
        n = np.abs(y2 - y1)
        for i in range(int(n+1)):
            y = y1 + i * (y2 - y1) / n
            x = np.round(x1 + i * (x2 - x1) / n)
            im[y, x] = colour

    return im


def plot_matches(im1, im2, matches):
    """
    Displays two images side by side with matches highlighted

    Args:
        im1, im2: paths to the two input images
        matches: 2D numpy array of size 4xN containing a list of matches (a
            list of pairs of points, each pair being represented by x1, y1, x2,
            y2)

    Returns:
        path to the resulting image, to be displayed
    """
    # load images
    img1 = piio.read(im1)
    img2 = piio.read(im2)

    # build the output image
    h1, w1 = img1.shape[:2]
    h2, w2 = img2.shape[:2]
    w = w1 + w2
    h = max(h1, h2)
    out = np.zeros((h, w, 3), np.float32)
    out[:h1, :w1] = img1
    out[:h2, w1:w] = img2

    # define colors, according to min/max intensity values
    out_min = min(np.min(img1), np.min(img2))
    out_max = max(np.max(img1), np.max(img2))
    green = [out_min, out_max, out_min]
    blue = [out_min, out_min, out_max]

    # plot the matches
    for i in range(len(matches)):
        x1 = matches[i, 0]
        y1 = matches[i, 1]
        x2 = matches[i, 2] + w1
        y2 = matches[i, 3]
        plot_line(out, x1, y1, x2, y2, blue)
        out[y1, x1] = green
        out[y2, x2] = green

    # save the output image, and return its path
    outfile = common.tmpfile('.tif')
    piio.write(outfile, out)
    return outfile


def plot_matches_pleiades(im1, im2, matches):
    """
    Plot matches on Pleiades images

    Args:
        im1, im2: paths to full Pleiades images
        matches: 2D numpy array of size 4xN containing a list of matches (a
            list of pairs of points, each pair being represented by x1, y1, x2,
            y2). The coordinates are given in the frame of the full images.

    Returns:
        path to the displayed output
    """
    # determine regions to crop in im1 and im2
    x1 = np.min(matches[:, 0])
    w1 = np.max(matches[:, 0]) - x1
    y1 = np.min(matches[:, 1])
    h1 = np.max(matches[:, 1]) - y1

    x2 = np.min(matches[:, 2])
    w2 = np.max(matches[:, 2]) - x2
    y2 = np.min(matches[:, 3])
    h2 = np.max(matches[:, 3]) - y2

    # add 20 pixels offset
    x1 -= 20
    y1 -= 20
    x2 -= 20
    y2 -= 20
    w1 += 40
    h1 += 40
    w2 += 40
    h2 += 40

    # do the crops
    crop1 = common.image_crop_TIFF(im1, x1, y1, w1, h1)
    crop2 = common.image_crop_TIFF(im2, x2, y2, w2, h2)

    # compute matches coordinates in the cropped images
    pts1 = matches[:, 0:2] - [x1, y1]
    pts2 = matches[:, 2:4] - [x2, y2]

    # plot the matches on the two crops
    to_display = plot_matches(crop1, crop2, np.hstack((pts1, pts2)))
    common.run('v %s' % (to_display))
    return