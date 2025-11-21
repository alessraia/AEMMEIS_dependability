package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.io.IOException;
import java.util.List;

@WebServlet("/aggiungi-libro")
public class AggiungiLibroRepartoServlet extends HttpServlet {
    private RepartoDAO repartoDAO;
    private LibroDAO libroService;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoDAO = repartoDAO;
    }

    public void setLibroDAO(LibroDAO libroDAO) {
        this.libroService = libroDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        if (repartoDAO == null) {
            repartoDAO = new RepartoDAO();
        }
        if (libroService == null) {
            libroService = new LibroDAO();
        }

        Reparto r = repartoDAO.doRetrieveById(Integer.parseInt(request.getParameter("idReparto")));
        request.setAttribute("reparto", r);

        List<Libro> libri = libroService.doRetriveAll();
        List<Libro> libriGiaPresenti = repartoDAO.getAppartenenza(r.getIdReparto());

        if(!libriGiaPresenti.isEmpty()){
            for(Libro l : libriGiaPresenti){
                libri.remove(l);
            }
        }
        request.setAttribute("libri", libri);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/reparti/stampaLibri.jsp");
        dispatcher.forward(request, response);
    }
}
