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

@WebServlet("/eliminaLibro-reparto")
public class EliminaLibroReparto extends HttpServlet {
    private RepartoDAO service;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.service = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
        String isbn= request.getParameter("isbn");
        String idParam = request.getParameter("idReparto");
        int idReparto;

        try {
            idReparto = Integer.parseInt(idParam);
        } catch (NumberFormatException ex) {
            log("Parametro 'id' non valido: " + idParam, ex);
            RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp");
            try {
                dispatcher.forward(request, response);
            } catch (ServletException | IOException e) {
                log("Errore durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);
            }
            return;
        }

        if (service == null) {
            service = new RepartoDAO();
        }
        service.deleteFromAppartenenzaLibro(idReparto, isbn);

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
