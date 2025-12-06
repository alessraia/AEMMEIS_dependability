package controller.admin.gestisciProdotti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import model.libroService.SedeDAO;

import java.io.IOException;
@WebServlet("/aggiungiLibro-reparto")
public class AggiungiLibroReparto extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String[] idReparti = request.getParameterValues("repartoSelezionato");
        String isbn = request.getParameter("isbn");

        RepartoDAO repartoService = new RepartoDAO();
        if(idReparti!=null) {
            for (String idReparto : idReparti) {
                int id;
                try {
                    id = Integer.parseInt(idReparto);
                    repartoService.doSaveAppartenenza(id,isbn);
                } catch (NumberFormatException ex) {
                    RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
                    try {
                        dispatcher.forward(request, response);
                    } catch (ServletException | IOException e) {
                        log("Errore durante il forward verso /WEB-INF/errorJsp/erroreForm.jsp", e);
                    }
                    return;
                }
            }
        }
        RequestDispatcher dispatcher = request.getRequestDispatcher("modifica-libro");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso modifica-libro", e);
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso modifica-libro", e);
        }

    }
}
