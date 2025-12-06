package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.*;

import java.io.IOException;
import java.util.List;

@WebServlet("/aggiungi-libro-sede")
public class AggiungiLibroSedeServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        SedeDAO sedeDAO = new SedeDAO();

        String idParam = request.getParameter("idSede");
        int idSede;

        try {
            idSede = Integer.parseInt(idParam);
        } catch (NumberFormatException ex) {
            log("Parametro 'id' non valido: " + idParam, ex);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/erroreForm.jsp", e);
            }
            return;
        }

        Sede s = sedeDAO.doRetrieveById(idSede);
        request.setAttribute("sede", s);

        LibroDAO libroService = new LibroDAO();
        List<Libro> libri = libroService.doRetriveAll();
        List<Libro> libriGiaPresenti = sedeDAO.getPresenza(s.getIdSede());

        if(!libriGiaPresenti.isEmpty()){
            for(Libro l : libriGiaPresenti){
                libri.remove(l);
            }
        }
        request.setAttribute("libri", libri);

        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/admin/sedi/stampaLibri.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward ", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward", e);
        }
    }
}
