/*
Name: Jingqi Yao
Studnet ID: 18268141
*/

#include <nori/accel.h>
#include <Eigen/Geometry>
#include <stack>


NORI_NAMESPACE_BEGIN

void Accel::addMesh(Mesh *mesh) {
    if (m_mesh)
        throw NoriException("Accel: only a single mesh is supported!");
    m_mesh = mesh;
    m_bbox = m_mesh->getBoundingBox();
}

void Accel::build() {
    std::vector<int> all_triangles;
    for (int i = 0; i < m_mesh->getTriangleCount(); i++) {
        all_triangles.push_back(i);
    }
    root = recursive_build(m_bbox, all_triangles, 0);
}

/* 2.1 */
Node *Accel::recursive_build(BoundingBox3f bbox, std::vector<int> triangles, int deepth) {
    // If no triangles
    if (triangles.size() == 0) {
        return nullptr;
    }
    Node *node = new Node();
    node->bbox = bbox;
    node->isLeaf = false;
    node->triangles = triangles;
    // If only few triangles
    if (triangles.size() < 10 || deepth > 10) {
        node->isLeaf = true;
        for (uint32_t i = 0; i < 8; i++) {
            node->child[i] = nullptr;
        }
        return node;
    }
    std::vector<int> trilist[8];
    // Divide Bounding Box
    BoundingBox3f *sub_bboxes[8];
    for (uint32_t i = 0; i < 8; i++) {
        Vector3f midpoint = bbox.getCenter();
        Vector3f corner = bbox.getCorner(i);
        Vector3f minpoint;
        Vector3f maxpoint;
        for (uint32_t j = 0; j < 3; j++) {
            minpoint[j] = std::min(midpoint[j], corner[j]);
            maxpoint[j] = std::max(midpoint[j], corner[j]);
        }
        sub_bboxes[i] = new BoundingBox3f(minpoint, maxpoint);
    }
    for (uint32_t i = 0; i < triangles.size(); i++) {
        BoundingBox3f tribox = m_mesh->getBoundingBox(triangles[i]);
        for (uint32_t j = 0; j < 8; j++) {
            if (sub_bboxes[j]->overlaps(tribox)) {
                trilist[j].push_back(triangles[i]);
            }
        }
    }
    for (uint32_t i = 0; i < 8; i++) {
        node->child[i] = recursive_build(*sub_bboxes[i], trilist[i], deepth + 1);
        delete sub_bboxes[i];
    }
    return node;
}

bool Accel::rayIntersect(const Ray3f &ray_, Intersection &its, bool shadowRay) const {
    bool foundIntersection = false;  // Was an intersection found so far?
    uint32_t f = (uint32_t) -1;      // Triangle index of the closest intersection

    Ray3f ray(ray_); /// Make a copy of the ray (we will need to update its '.maxt' value)

    /* Brute force search through all triangles */
    // for (uint32_t idx = 0; idx < m_mesh->getTriangleCount(); ++idx) {
    //     float u, v, t;
    //     if (m_mesh->rayIntersect(idx, ray, u, v, t)) {
    //         /* An intersection was found! Can terminate
    //            immediately if this is a shadow ray query */
    //         if (shadowRay)
    //             return true;
    //         ray.maxt = its.t = t;
    //         its.uv = Point2f(u, v);
    //         its.mesh = m_mesh;
    //         f = idx;
    //         foundIntersection = true;
    //     }
    // }

    std::stack<Node*> node_stack;
    node_stack.push(root);
    /* 2.2 */
    // while (!node_stack.empty()) {
    while (!node_stack.empty() && !foundIntersection) {
        Node *current_node = node_stack.top();
        node_stack.pop();
        if (current_node && current_node->bbox.rayIntersect(ray)) {
            if (current_node->isLeaf) {
                for (uint32_t i = 0; i < current_node->triangles.size(); i++) {
                    uint32_t idx = current_node->triangles[i];
                    float u, v, t;
                    if (m_mesh->rayIntersect(idx, ray, u, v, t)) {
                        /* An intersection was found! Can terminate
                        immediately if this is a shadow ray query */
                        if (shadowRay)
                            return true;
                        ray.maxt = its.t = t;
                        its.uv = Point2f(u, v);
                        its.mesh = m_mesh;
                        f = idx;
                        foundIntersection = true;
                        /* comment next line for 2.2 */
                        break;
                    }
                }
            } else {
                /* 2.3 */
                std::pair<float, Node *> distances[8];
                for (int i = 0; i < 8; i++) {
                    if (current_node->child[i]) {
                        distances[i].first = current_node->child[i]->bbox.distanceTo(ray.o);
                        distances[i].second = current_node->child[i];
                    } else {
                        distances[i].first = 0;
                        distances[i].second = nullptr;
                    }
                }
                std::sort(std::begin(distances), std::end(distances), [](std::pair<float, Node *> &p1, std::pair<float, Node *> &p2) {
                    return p1.first > p2.first;
                });
                for (uint32_t i = 0; i < 8; i++) {
                    if (distances[i].second) {
                        node_stack.push(distances[i].second);
                    }
                }
                /* 2.2 simple traversal */
                // for (uint32_t i = 0; i < 8; i++) {
                //     if (current_node->child[i]) {
                //         node_stack.push(current_node->child[i]);
                //     }
                // }
            }
        }
    }

    if (foundIntersection) {
        /* At this point, we now know that there is an intersection,
           and we know the triangle index of the closest such intersection.

           The following computes a number of additional properties which
           characterize the intersection (normals, texture coordinates, etc..)
        */

        /* Find the barycentric coordinates */
        Vector3f bary;
        bary << 1-its.uv.sum(), its.uv;

        /* References to all relevant mesh buffers */
        const Mesh *mesh   = its.mesh;
        const MatrixXf &V  = mesh->getVertexPositions();
        const MatrixXf &N  = mesh->getVertexNormals();
        const MatrixXf &UV = mesh->getVertexTexCoords();
        const MatrixXu &F  = mesh->getIndices();

        /* Vertex indices of the triangle */
        uint32_t idx0 = F(0, f), idx1 = F(1, f), idx2 = F(2, f);

        Point3f p0 = V.col(idx0), p1 = V.col(idx1), p2 = V.col(idx2);

        /* Compute the intersection positon accurately
           using barycentric coordinates */
        its.p = bary.x() * p0 + bary.y() * p1 + bary.z() * p2;

        /* Compute proper texture coordinates if provided by the mesh */
        if (UV.size() > 0)
            its.uv = bary.x() * UV.col(idx0) +
                bary.y() * UV.col(idx1) +
                bary.z() * UV.col(idx2);

        /* Compute the geometry frame */
        its.geoFrame = Frame((p1-p0).cross(p2-p0).normalized());

        if (N.size() > 0) {
            /* Compute the shading frame. Note that for simplicity,
               the current implementation doesn't attempt to provide
               tangents that are continuous across the surface. That
               means that this code will need to be modified to be able
               use anisotropic BRDFs, which need tangent continuity */

            its.shFrame = Frame(
                (bary.x() * N.col(idx0) +
                 bary.y() * N.col(idx1) +
                 bary.z() * N.col(idx2)).normalized());
        } else {
            its.shFrame = its.geoFrame;
        }
    }

    return foundIntersection;
}

NORI_NAMESPACE_END

