package controller.admin.gestisciSedi;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.RepartoDAO;
import model.libroService.SedeDAO;

import java.io.IOException;

@WebServlet("/insert-libroSede")
public class InsertLibroSedeServlet extends HttpServlet {
    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
        String[] libriIsbn = (request.getParameterValues("isbn"));
        SedeDAO sedeDAO = new SedeDAO();
        if(libriIsbn!=null){
            for(String isbn : libriIsbn){

                String idParam = request.getParameter("idSede");
                int idSede;

                try {
                    idSede = Integer.parseInt(idParam);
                    sedeDAO.addLibroSede(sedeDAO.doRetrieveById(idSede), isbn);
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


            }
        }
        response.sendRedirect("gestisci-sedi");
    }
}